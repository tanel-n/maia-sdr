//! IIO device access.
//!
//! This module is used to control IIO devices, such as the ADI AD9361 driver.

use anyhow::{Context, Result};
use std::path::{Path, PathBuf};
use tokio::fs;

/// AD9361 IIO device.
///
/// This struct represents the AD9361 IIO device (ad9361-phy) and can be used to
/// control its attributes.
#[derive(Debug)]
pub struct Ad9361 {
    iio_device_path: PathBuf,
}

macro_rules! iio_getset {
    ($attribute:ident, $filename:expr, $ty_internal:ty, $ty_external:ty) => {
        paste::paste! {
            #[doc = concat!("Returns the value of the `", stringify!($attribute),
                            "` IIO attribute.")]
            pub async fn [<get_ $attribute>](&self) -> Result<$ty_external> {
                fs::read_to_string(self.iio_device_path.join($filename))
                    .await?
                    .trim_end()
                    .parse::<$ty_internal>()
                    .map_err(|_| anyhow::anyhow!(concat!(
                        "failed to parse IIO attribute ", stringify!($attribute))))
                    .map(|x| x.into())
            }

            #[doc = concat!("Sets the value of the `", stringify!($attribute),
                            "` IIO attribute.")]
            pub async fn [<set_ $attribute>](&self, value: $ty_external) -> Result<()> {
                fs::write(
                    self.iio_device_path.join($filename),
                    Into::<$ty_internal>::into(value).to_string().as_bytes(),
                ).await.context(concat!("failed to set IIO attribute ",
                                        stringify!($attribute)))?;
                Ok(())
            }
        }
    };
}

impl Ad9361 {
    /// Opens an AD9361 IIO device.
    ///
    /// This function opens the first IIO device with name ad9361-phy that is
    /// found in the system.
    pub async fn new() -> Result<Ad9361> {
        let iio_device_path = Self::find_iio_device()
            .await?
            .ok_or_else(|| anyhow::anyhow!("ad9361-phy IIO device not found"))?;
        Ok(Ad9361 { iio_device_path })
    }

    async fn find_iio_device() -> Result<Option<PathBuf>> {
        let mut entries = fs::read_dir(Path::new("/sys/bus/iio/devices")).await?;
        while let Some(entry) = entries.next_entry().await? {
            if entry
                .file_name()
                .to_str()
                .ok_or_else(|| anyhow::anyhow!("file name is not valid UTF8"))?
                .starts_with("iio:device")
            {
                let mut path = entry.path();
                path.push("name");
                let this_name = fs::read_to_string(path).await?;
                if this_name == "ad9361-phy\n" {
                    return Ok(Some(entry.path()));
                }
            }
        }
        Ok(None)
    }

    iio_getset!(
        sampling_frequency,
        "in_voltage_sampling_frequency",
        u32,
        u32
    );
    iio_getset!(rx_rf_bandwidth, "in_voltage_rf_bandwidth", u32, u32);

    /// Returns the value of the tx_rf_bandwidth IIO attribute.
    pub async fn get_tx_rf_bandwidth(&self) -> Result<u32> {
        fs::read_to_string(self.iio_device_path.join("out_voltage_rf_bandwidth"))
            .await?
            .trim_end()
            .parse::<u32>()
            .map_err(|_| anyhow::anyhow!("failed to parse IIO attribute tx_rf_bandwidth"))
    }

    /// Sets the value of the tx_rf_bandwidth IIO attribute and ensures the
    /// TX sampling frequency is set to 5 Msps (required for the tone generator).
    pub async fn set_tx_rf_bandwidth(&self, value: u32) -> Result<()> {
        // Set RF bandwidth
        fs::write(
            self.iio_device_path.join("out_voltage_rf_bandwidth"),
            value.to_string().as_bytes(),
        )
        .await
        .context("failed to set IIO attribute tx_rf_bandwidth")?;

        fs::write(
            self.iio_device_path.join("out_voltage_sampling_frequency"),
            "5000000".as_bytes(),
        )
        .await
        .context("failed to set out_voltage_sampling_frequency to 5 Msps")?;

        Ok(())
    }

    iio_getset!(rx_lo_frequency, "out_altvoltage0_RX_LO_frequency", u64, u64);
    iio_getset!(tx_lo_frequency, "out_altvoltage1_TX_LO_frequency", u64, u64);
    iio_getset!(rx_gain, "in_voltage0_hardwaregain", Dbf64, f64);
    iio_getset!(tx_gain, "out_voltage0_hardwaregain", Dbf64, f64);
    iio_getset!(
        rx_gain_mode,
        "in_voltage0_gain_control_mode",
        Ad9361GainMode,
        Ad9361GainMode
    );

    /// Returns the value of the loopback IIO attribute.
    pub async fn get_loopback_mode(&self) -> Result<Ad9361LoopbackMode> {
        let path = std::path::Path::new("/sys/kernel/debug/iio/iio:device0/loopback");
        match fs::read_to_string(path).await {
            Ok(s) => {
                let v = s.trim().parse::<u32>().unwrap_or(0);
                Ok(Ad9361LoopbackMode::from(v))
            }
            Err(e) => {
                // If file missing or unreadable, assume disabled rather than erroring.
                if e.kind() == std::io::ErrorKind::NotFound {
                    return Ok(Ad9361LoopbackMode::from(0));
                }
                Err(e).context("failed to read loopback debugfs")?
            }
        }
    }

    /// Sets the value of the loopback IIO attribute.
    pub async fn set_loopback_mode(&self, value: Ad9361LoopbackMode) -> Result<()> {
        let path = std::path::Path::new("/sys/kernel/debug/iio/iio:device0/loopback");
        let v: u32 = value.into();
        fs::write(path, v.to_string().as_bytes())
            .await
            .with_context(|| format!("failed to write loopback at {:?}", path))?;
        Ok(())
    }

    /// Returns the value of the tx_tone_enabled IIO attribute.
    pub async fn get_tx_tone_enabled(&self) -> Result<bool> {
        let path = self
            .iio_device_path
            .join("../iio:device3/out_altvoltage0_TX1_I_F1_scale");
        match fs::read_to_string(&path).await {
            Ok(s) => {
                let val: f32 = s.trim().parse().unwrap_or(0.0);
                Ok(val > 0.0)
            }
            Err(e) => {
                if e.kind() == std::io::ErrorKind::NotFound {
                    return Ok(false);
                }
                Err(e).with_context(|| format!("Missing DDS scale file at {:?}", path))?
            }
        }
    }

    /// Sets the value of the tx_tone_enabled IIO attribute.
    /// When enabling this also configures DDS I/Q frequency offsets, Q phase,
    /// enables the I/Q channels and sets their scales to 0.25. When disabling
    /// it disables the channels and clears the scales.
    pub async fn set_tx_tone_enabled(&self, value: bool) -> Result<()> {
        let base = self.iio_device_path.join("../iio:device3");

        // Files to set for enabling the tone
        let i_freq = base.join("out_altvoltage0_TX1_I_F1_frequency");
        let q_freq = base.join("out_altvoltage2_TX1_Q_F1_frequency");
        let q_phase = base.join("out_altvoltage2_TX1_Q_F1_phase");
        let i_raw = base.join("out_altvoltage0_TX1_I_F1_raw");
        let q_raw = base.join("out_altvoltage2_TX1_Q_F1_raw");
        let i_scale = base.join("out_altvoltage0_TX1_I_F1_scale");
        let q_scale = base.join("out_altvoltage2_TX1_Q_F1_scale");

        if value {
            fs::write(&i_freq, "100000".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", i_freq))?;
            fs::write(&q_freq, "100000".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_freq))?;
            fs::write(&q_phase, "90000".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_phase))?;

            fs::write(&i_raw, "1".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", i_raw))?;
            fs::write(&q_raw, "1".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_raw))?;

            fs::write(&i_scale, "0.25".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", i_scale))?;
            fs::write(&q_scale, "0.25".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_scale))?;
        } else {
            // Disable transmission
            fs::write(&i_raw, "0".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", i_raw))?;
            fs::write(&q_raw, "0".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_raw))?;

            fs::write(&i_scale, "0".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", i_scale))?;
            fs::write(&q_scale, "0".as_bytes())
                .await
                .with_context(|| format!("Failed to write to {:?}", q_scale))?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
/// AD9361 gain control modes.
///
/// This enum lists the automatic gain control modes supported by the AD9361.
pub struct Ad9361GainMode(maia_json::Ad9361GainMode);

impl From<maia_json::Ad9361GainMode> for Ad9361GainMode {
    fn from(value: maia_json::Ad9361GainMode) -> Ad9361GainMode {
        Ad9361GainMode(value)
    }
}

impl From<Ad9361GainMode> for maia_json::Ad9361GainMode {
    fn from(value: Ad9361GainMode) -> maia_json::Ad9361GainMode {
        value.0
    }
}

impl std::str::FromStr for Ad9361GainMode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "manual" => maia_json::Ad9361GainMode::Manual,
            "fast_attack" => maia_json::Ad9361GainMode::FastAttack,
            "slow_attack" => maia_json::Ad9361GainMode::SlowAttack,
            "hybrid" => maia_json::Ad9361GainMode::Hybrid,
            _ => return Err(()),
        }
        .into())
    }
}

impl std::fmt::Display for Ad9361GainMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self.0 {
                maia_json::Ad9361GainMode::Manual => "manual",
                maia_json::Ad9361GainMode::FastAttack => "fast_attack",
                maia_json::Ad9361GainMode::SlowAttack => "slow_attack",
                maia_json::Ad9361GainMode::Hybrid => "hybrid",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
/// AD9361 loopback modes (wrapper around maia_json::Ad9361LoopbackMode).
pub struct Ad9361LoopbackMode(maia_json::Ad9361LoopbackMode);

impl From<maia_json::Ad9361LoopbackMode> for Ad9361LoopbackMode {
    fn from(value: maia_json::Ad9361LoopbackMode) -> Ad9361LoopbackMode {
        Ad9361LoopbackMode(value)
    }
}

impl From<Ad9361LoopbackMode> for maia_json::Ad9361LoopbackMode {
    fn from(value: Ad9361LoopbackMode) -> maia_json::Ad9361LoopbackMode {
        value.0
    }
}

impl From<u32> for Ad9361LoopbackMode {
    fn from(value: u32) -> Self {
        // Map numeric loopback representation -> JSON enum
        let v = match value {
            1 => maia_json::Ad9361LoopbackMode::Digital,
            2 => maia_json::Ad9361LoopbackMode::Rf,
            _ => maia_json::Ad9361LoopbackMode::Disabled,
        };
        v.into()
    }
}

impl From<Ad9361LoopbackMode> for u32 {
    fn from(value: Ad9361LoopbackMode) -> u32 {
        match value.0 {
            maia_json::Ad9361LoopbackMode::Disabled => 0,
            maia_json::Ad9361LoopbackMode::Digital => 1,
            maia_json::Ad9361LoopbackMode::Rf => 2,
        }
    }
}

impl std::str::FromStr for Ad9361LoopbackMode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "disabled" => maia_json::Ad9361LoopbackMode::Disabled,
            "digital" => maia_json::Ad9361LoopbackMode::Digital,
            "rf" | "RF" => maia_json::Ad9361LoopbackMode::Rf,
            _ => return Err(()),
        }
        .into())
    }
}

impl std::fmt::Display for Ad9361LoopbackMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self.0 {
                maia_json::Ad9361LoopbackMode::Disabled => "disabled",
                maia_json::Ad9361LoopbackMode::Digital => "digital",
                maia_json::Ad9361LoopbackMode::Rf => "rf",
            }
        )
    }
}

#[derive(Debug, Clone, Copy)]
struct Dbf64(f64);

impl From<f64> for Dbf64 {
    fn from(value: f64) -> Dbf64 {
        Dbf64(value)
    }
}

impl From<Dbf64> for f64 {
    fn from(value: Dbf64) -> f64 {
        value.0
    }
}

impl std::str::FromStr for Dbf64 {
    type Err = <f64 as std::str::FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let db = " dB";
        if !s.ends_with(db) {
            return Err(format!("{s} does not end with 'dB'")
                .parse::<f64>()
                .err()
                .unwrap());
        }
        s[..s.len() - db.len()].parse().map(Dbf64)
    }
}

impl std::fmt::Display for Dbf64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

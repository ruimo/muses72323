//! # muses72323
//!
//! A Rust driver library for the MUSES72323 electronic volume controller IC.
//!
//! This crate provides type-safe command structures for controlling the MUSES72323,
//! a high-quality 2-channel electronic volume controller with the following features:
//!
//! - Volume control: 0dB to -111.75dB (0.25dB steps)
//! - Gain control: 0dB to +21dB (+3dB steps)
//! - Soft step function to reduce zipper noise
//! - Zero-cross detection
//! - Independent or linked L/R channel control
//!
//! ## Usage
//!
//! ```rust
//! use muses72323::commands::{SetVolume, SetGain, SoftClock, Channel, Gain, ClockDiv, ZeroWindowVolt};
//!
//! // Set volume to -20dB (80 steps of 0.25dB)
//! let volume_cmd = SetVolume::new()
//!     .with_chip_addr(0b00)
//!     .with_channel(Channel::LorBoth)
//!     .with_is_soft_step(true)
//!     .with_volume(80);
//!
//! // Set gain to +12dB for both channels
//! let gain_cmd = SetGain::new()
//!     .with_chip_addr(0b00)
//!     .with_l_gain(Gain::Gain12db)
//!     .with_r_gain(Gain::Gain12db)
//!     .with_l_r_cont(true)
//!     .with_zero_cross_off(false);
//!
//! // Configure soft clock with internal clock and 1/32 division
//! let clock_cmd = SoftClock::new()
//!     .with_chip_addr(0b00)
//!     .with_internal_clock(true)
//!     .with_clock_div(ClockDiv::Div32)
//!     .with_zero_window_volt(ZeroWindowVolt::Mul4);
//!
//! // Convert to u16 for transmission
//! let volume_data: u16 = volume_cmd.into();
//! let gain_data: u16 = gain_cmd.into();
//! let clock_data: u16 = clock_cmd.into();
//! ```
//!
//! ## Commands
//!
//! The crate provides three main command structures:
//!
//! - [`SetVolume`](commands::SetVolume): Control volume level with soft step option
//! - [`SetGain`](commands::SetGain): Control gain and L/R channel linking
//! - [`SoftClock`](commands::SoftClock): Configure clock settings and zero-cross detection
//!
//! All commands are converted to 16-bit values for transmission to the MUSES72323 IC.

pub mod commands;

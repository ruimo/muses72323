use bitfield_struct::bitfield;

/// Volume level value (0 to 447)
///
/// Maps to actual hardware values:
/// - `0` → 479 (-111.75dB, minimum volume)
/// - `1` → 478 (-111.5dB)
/// - `2` → 477 (-111.25dB)
/// - ...
/// - `447` → 32 (0dB, maximum volume)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VolumeValue(u16);

/// Error type for invalid volume level values
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidVolumeValueError(u16);

impl core::fmt::Display for InvalidVolumeValueError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Invalid volume level value: {}. Must be in range 0-447",
            self.0
        )
    }
}

impl std::error::Error for InvalidVolumeValueError {}

impl VolumeValue {
    /// Maximum volume level value
    pub const MAX: u16 = Volume::MAX_HW - Volume::MIN_HW;

    /// Converts to the actual hardware value (32-479)
    ///
    /// # Returns
    /// Hardware value in range 32-479
    ///
    /// # Examples
    /// ```
    /// use muses72323::commands::{VolumeValue, Volume};
    /// use core::convert::TryFrom;
    ///
    /// let vol = VolumeValue::try_from(0).unwrap();
    /// assert_eq!(vol.to_hardware_value(), Volume::MAX_HW); // 0 → 479 (min)
    ///
    /// let vol = VolumeValue::try_from(447).unwrap();
    /// assert_eq!(vol.to_hardware_value(), Volume::MIN_HW);  // 447 → 32 (max)
    /// ```
    pub const fn to_hardware_value(self) -> u16 {
        Volume::MAX_HW - self.0
    }

    /// Creates from hardware value (32-479)
    ///
    /// # Arguments
    /// * `hw_value` - Hardware value (32-479)
    ///
    /// # Returns
    /// `Ok(VolumeValue)` if valid, `Err` otherwise
    pub const fn from_hardware_value(hw_value: u16) -> Result<Self, InvalidVolumeValueError> {
        if hw_value >= Volume::MIN_HW && hw_value <= Volume::MAX_HW {
            Ok(VolumeValue(Volume::MAX_HW - hw_value))
        } else {
            Err(InvalidVolumeValueError(hw_value))
        }
    }

    /// Gets the raw value (0-447)
    pub const fn get(self) -> u16 {
        self.0
    }
}

impl TryFrom<u16> for VolumeValue {
    type Error = InvalidVolumeValueError;

    /// Attempts to create a VolumeValue from a u16
    ///
    /// # Arguments
    /// * `value` - Volume level (0-447)
    ///
    /// # Examples
    /// ```
    /// use muses72323::commands::VolumeValue;
    /// use core::convert::TryFrom;
    ///
    /// let min_volume = VolumeValue::try_from(0).unwrap();   // -111.75dB
    /// let max_volume = VolumeValue::try_from(447).unwrap(); // 0dB
    /// assert!(VolumeValue::try_from(448).is_err());         // Out of range
    /// ```
    fn try_from(value: u16) -> Result<Self, Self::Error> {
        if value <= Self::MAX {
            Ok(VolumeValue(value))
        } else {
            Err(InvalidVolumeValueError(value))
        }
    }
}

impl From<VolumeValue> for u16 {
    fn from(value: VolumeValue) -> Self {
        value.0
    }
}

/// Volume value for SetVolume command
///
/// Valid values are:
/// - `Mute0`: MUTE (0b000000000)
/// - `Mute511`: MUTE (0b111111111)
/// - `Volume(VolumeValue)`: Valid volume range from 0 (-111.75dB) to 447 (0dB), maps to hardware values MIN_RAW_VOLUME-MAX_RAW_VOLUME
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Volume {
    /// Mute (value: 0)
    Mute0,
    /// Mute (value: 511)
    Mute511,
    /// Volume level (0-447, maps to hardware values MIN_RAW_VOLUME-MAX_RAW_VOLUME)
    Volume(VolumeValue),
}

/// Error type for invalid volume values
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidVolumeError(u16);

impl core::fmt::Display for InvalidVolumeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Invalid volume value: {}. Must be 0, 511, or in range {}-{}",
            self.0, Volume::MIN_HW, Volume::MAX_HW
        )
    }
}

impl std::error::Error for InvalidVolumeError {}

impl Volume {
    /// Minimum valid hardware volume value (excluding mute)
    pub const MIN_HW: u16 = 32;
    
    /// Maximum valid hardware volume value (excluding mute)
    pub const MAX_HW: u16 = 479;

    /// Converts the volume to its bit representation
    ///
    /// # Returns
    /// A 9-bit value (0-511)
    ///
    /// # Examples
    /// ```
    /// use muses72323::commands::{Volume, VolumeValue};
    /// use core::convert::TryFrom;
    ///
    /// assert_eq!(Volume::Mute0.into_bits(), 0);
    /// assert_eq!(Volume::Mute511.into_bits(), 511);
    ///
    /// let vol = VolumeValue::try_from(0).unwrap();
    /// assert_eq!(Volume::Volume(vol).into_bits(), Volume::MAX_HW);
    ///
    /// let vol = VolumeValue::try_from(447).unwrap();
    /// assert_eq!(Volume::Volume(vol).into_bits(), Volume::MIN_HW);
    /// ```
    pub const fn into_bits(self) -> u16 {
        match self {
            Volume::Mute0 => 0,
            Volume::Mute511 => 0b111111111,
            Volume::Volume(v) => v.to_hardware_value(),
        }
    }

    /// Checks if this volume represents mute
    ///
    /// # Returns
    /// `true` if the volume is `Mute0` or `Mute511`, `false` otherwise
    ///
    /// # Examples
    /// ```
    /// use muses72323::commands::{Volume, VolumeValue};
    /// use core::convert::TryFrom;
    ///
    /// assert!(Volume::Mute0.is_mute());
    /// assert!(Volume::Mute511.is_mute());
    ///
    /// let vol = VolumeValue::try_from(100).unwrap();
    /// assert!(!Volume::Volume(vol).is_mute());
    /// ```
    pub const fn is_mute(self) -> bool {
        matches!(self, Volume::Mute0 | Volume::Mute511)
    }
}

impl TryFrom<u16> for Volume {
    type Error = InvalidVolumeError;

    /// Attempts to create a Volume from a u16 hardware value
    ///
    /// # Arguments
    /// * `value` - Hardware volume value (9 bits, 0-511)
    ///
    /// # Returns
    /// - `Ok(Volume)` if the value is valid (0, 32-479, or 511)
    /// - `Err(InvalidVolumeError)` if the value is invalid
    ///
    /// # Examples
    /// ```
    /// use muses72323::commands::Volume;
    /// use core::convert::TryFrom;
    ///
    /// // Valid values
    /// assert_eq!(Volume::try_from(0).unwrap(), Volume::Mute0);
    /// assert_eq!(Volume::try_from(511).unwrap(), Volume::Mute511);
    ///
    /// // Hardware values roundtrip correctly
    /// let vol = Volume::try_from(Volume::MIN_HW).unwrap();
    /// assert_eq!(vol.into_bits(), Volume::MIN_HW);
    ///
    /// let vol = Volume::try_from(Volume::MAX_HW).unwrap();
    /// assert_eq!(vol.into_bits(), Volume::MAX_HW);
    ///
    /// // Invalid values
    /// assert!(Volume::try_from(1).is_err());   // Between 1-31
    /// assert!(Volume::try_from(31).is_err());  // Between 1-31
    /// assert!(Volume::try_from(480).is_err()); // Between 480-510
    /// assert!(Volume::try_from(510).is_err()); // Between 480-510
    /// ```
    fn try_from(value: u16) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Volume::Mute0),
            0b111111111 => Ok(Volume::Mute511),
            v if v >= Self::MIN_HW && v <= Self::MAX_HW => {
                Ok(Volume::Volume(VolumeValue(Self::MAX_HW - v)))
            }
            _ => Err(InvalidVolumeError(value)),
        }
    }
}

impl From<Volume> for u16 {
    fn from(volume: Volume) -> Self {
        volume.into_bits()
    }
}

/// Channel
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Channel {
    /// L channel if [`SetGain`]'s [`l_r_cont`](crate::commands::SetGain::l_r_cont) is false. Both channels if [`l_r_cont`](crate::commands::SetGain::l_r_cont) is true.
    LorBoth = 0,
    /// R channel. Cannot be specified when [`SetGain`]'s [`l_r_cont`](crate::commands::SetGain::l_r_cont) is true.
    R = 1,
}

impl Channel {
    /// Converts the channel enum to its bit representation.
    ///
    /// # Returns
    /// - `0` for `LorBoth`
    /// - `1` for `R`
    pub const fn into_bits(self) -> u8 {
        self as u8
    }

    /// Creates a channel enum from a bit value.
    ///
    /// # Arguments
    /// * `value` - A value in the range 0-1 (2 bits)
    ///
    /// # Returns
    /// The corresponding `Channel` value. Returns `LorBoth` for out-of-range values.
    pub const fn from_bits(value: u8) -> Self {
        match value {
            0 => Channel::LorBoth,
            1 => Channel::R,
            _ => Channel::LorBoth, // Default value
        }
    }
}

/// Volume setting command
///
/// # Builder Methods
///
/// This struct provides builder methods generated by the `bitfield-struct` crate:
/// - `new()` - Creates a new instance with default values
/// - `with_chip_addr(u8)` - Sets the chip address (2 bits)
/// - `with_channel(Channel)` - Sets the channel
/// - `with_is_soft_step(bool)` - Enables/disables soft step circuit
/// - `with_volume(u16)` - Sets the volume using raw hardware value (9 bits, 0-511)
///
/// Additional helper methods:
/// - `safe_with_volume(Volume)` - Sets the volume using the type-safe Volume type
/// - `volume_value()` - Gets the volume as a Volume type (returns Result)
///
/// # Example
///
/// ```
/// use muses72323::commands::{SetVolume, Channel, Volume, VolumeValue};
/// use core::convert::TryFrom;
///
/// // Using typed Volume (type-safe)
/// let vol = VolumeValue::try_from(100).unwrap();
/// let cmd = SetVolume::new()
///     .with_chip_addr(0b11)
///     .with_channel(Channel::R)
///     .with_is_soft_step(true)
///     .safe_with_volume(Volume::Volume(vol));
///
/// // Using mute
/// let cmd2 = SetVolume::new()
///     .with_chip_addr(0b11)
///     .with_channel(Channel::R)
///     .with_is_soft_step(true)
///     .safe_with_volume(Volume::Mute0);
///
/// let raw: u16 = cmd.into();
/// ```
#[bitfield(u16)]
pub struct SetVolume {
    /// Chip address. Must match the state of ADR0, ADR1 (chip address selection pins).
    #[bits(2)]
    pub chip_addr: u8,
    /// Channel.
    #[bits(2)]
    pub channel: Channel,
    /// Soft step circuit ON/OFF control.
    /// The soft step function reduces zipper noise during gain adjustment by changing the gain setting gradually.
    pub is_soft_step: bool,
    /// Fixed to 0
    #[bits(2)]
    __: u8,
    /// Controls each volume from 0dB to -111.75dB (0.25dB step).
    /// Each volume is controlled independently when L/R Cont="0".
    /// Use `safe_with_volume()` for type-safe setting with Volume type.
    #[bits(9)]
    pub volume: u16,
}

impl SetVolume {
    /// Sets the volume using the type-safe Volume type
    ///
    /// # Arguments
    /// * `vol` - Volume value (Mute0, Mute511, or Volume(VolumeValue))
    ///
    /// # Example
    /// ```
    /// use muses72323::commands::{SetVolume, Volume, VolumeValue};
    /// use core::convert::TryFrom;
    ///
    /// let vol = VolumeValue::try_from(200).unwrap();
    /// let cmd = SetVolume::new().safe_with_volume(Volume::Volume(vol));
    ///
    /// let mute_cmd = SetVolume::new().safe_with_volume(Volume::Mute0);
    /// ```
    pub const fn safe_with_volume(self, vol: Volume) -> Self {
        self.with_volume(vol.into_bits())
    }

    /// Gets the volume as a Volume type
    ///
    /// # Returns
    /// - `Ok(Volume)` if the stored value is valid
    /// - `Err(InvalidVolumeError)` if the stored value is invalid
    ///
    /// # Example
    /// ```
    /// use muses72323::commands::{SetVolume, Volume};
    ///
    /// let vol = Volume::Mute0;
    /// let cmd = SetVolume::new().safe_with_volume(vol);
    /// let retrieved = cmd.volume_value().unwrap();
    /// assert_eq!(retrieved, vol);
    /// ```
    pub fn volume_value(self) -> Result<Volume, InvalidVolumeError> {
        Volume::try_from(self.volume())
    }
}

/// Represents gain specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Gain {
    /// 0dB
    Gain0 = 0,
    /// +3dB
    Gain3db = 1,
    /// +6dB
    Gain6db = 2,
    /// +9dB
    Gain9db = 3,
    /// +12dB
    Gain12db = 4,
    /// +15dB
    Gain15db = 5,
    /// +18dB
    Gain18db = 6,
    /// +21dB
    Gain21db = 7,
}

impl Gain {
    /// Converts the gain enum to its bit representation.
    ///
    /// # Returns
    /// A 3-bit value (0-7) representing the gain level:
    /// - `0` = 0dB
    /// - `1` = +3dB
    /// - `2` = +6dB
    /// - `3` = +9dB
    /// - `4` = +12dB
    /// - `5` = +15dB
    /// - `6` = +18dB
    /// - `7` = +21dB
    pub const fn into_bits(self) -> u8 {
        self as u8
    }

    /// Creates a gain enum from a bit value.
    ///
    /// # Arguments
    /// * `value` - A value in the range 0-7 (3 bits)
    ///
    /// # Returns
    /// The corresponding `Gain` value. Returns `Gain0` for out-of-range values.
    pub const fn from_bits(value: u8) -> Self {
        match value {
            0 => Gain::Gain0,
            1 => Gain::Gain3db,
            2 => Gain::Gain6db,
            3 => Gain::Gain9db,
            4 => Gain::Gain12db,
            5 => Gain::Gain15db,
            6 => Gain::Gain18db,
            7 => Gain::Gain21db,
            _ => Gain::Gain0, // Default value
        }
    }
}

/// Gain setting command
///
/// # Builder Methods
///
/// This struct provides builder methods generated by the `bitfield-struct` crate:
/// - `new()` - Creates a new instance with default values
/// - `with_chip_addr(u8)` - Sets the chip address (2 bits)
/// - `with_zero_cross_off(bool)` - Turns off zero-cross detection circuit
/// - `with_r_gain(Gain)` - Sets right channel gain
/// - `with_l_gain(Gain)` - Sets left channel gain
/// - `with_l_r_cont(bool)` - Sets independent/linked control of L/R channels
///
/// # Example
///
/// ```
/// use muses72323::commands::{SetGain, Gain};
///
/// let cmd = SetGain::new()
///     .with_chip_addr(0b10)
///     .with_zero_cross_off(true)
///     .with_r_gain(Gain::Gain15db)
///     .with_l_gain(Gain::Gain9db)
///     .with_l_r_cont(false);
///
/// let raw: u16 = cmd.into();
/// ```
#[bitfield(u16)]
pub struct SetGain {
    /// Chip address. Must match the state of ADR0, ADR1 (chip address selection pins).
    #[bits(2)]
    pub chip_addr: u8,
    /// Fixed to 0b000010.
    #[bits(6, default = 0b000010)]
    __: u8,
    /// Turn off zero-cross detection circuit.
    pub zero_cross_off: bool,
    /// Controls right channel gain from 0dB to +21dB (+3dB/step).
    #[bits(3)]
    pub r_gain: Gain,
    /// Controls left channel gain from 0dB to +21dB (+3dB/step).
    #[bits(3)]
    pub l_gain: Gain,
    /// Sets independent/linked control of L channel Volume and R channel Volume.
    pub l_r_cont: bool,
}

/// Clock division ratio
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ClockDiv {
    /// No division (1/1)
    Div1 = 0,
    /// 1/4 division
    Div4 = 1,
    /// 1/8 division
    Div8 = 2,
    /// 1/16 division
    Div16 = 3,
    /// 1/32 division
    Div32 = 4,
    /// 1/64 division
    Div64 = 5,
    /// 1/128 division
    Div128 = 6,
    /// 1/256 division
    Div256 = 7,
}

impl ClockDiv {
    /// Converts the clock division enum to its bit representation.
    ///
    /// # Returns
    /// A 3-bit value (0-7) representing the division ratio:
    /// - `0` = 1/1 (no division)
    /// - `1` = 1/4
    /// - `2` = 1/8
    /// - `3` = 1/16
    /// - `4` = 1/32
    /// - `5` = 1/64
    /// - `6` = 1/128
    /// - `7` = 1/256
    pub const fn into_bits(self) -> u8 {
        self as u8
    }

    /// Creates a clock division enum from a bit value.
    ///
    /// # Arguments
    /// * `value` - A value in the range 0-7 (3 bits)
    ///
    /// # Returns
    /// The corresponding `ClockDiv` value. Returns `Div1` for out-of-range values.
    pub const fn from_bits(value: u8) -> Self {
        match value {
            0 => ClockDiv::Div1,
            1 => ClockDiv::Div4,
            2 => ClockDiv::Div8,
            3 => ClockDiv::Div16,
            4 => ClockDiv::Div32,
            5 => ClockDiv::Div64,
            6 => ClockDiv::Div128,
            7 => ClockDiv::Div256,
            _ => ClockDiv::Div1, // Default value
        }
    }
}

/// Zero-cross detection voltage width
///
/// Sets the window voltage for zero-cross detection.
/// This value specifies the multiplier of the voltage range where a signal is judged as zero-cross.
/// The larger the value, the lower the sensitivity of zero-cross detection (considers a wider voltage range as zero).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ZeroWindowVolt {
    /// 1x reference voltage (highest sensitivity)
    Mul1 = 0,
    /// 2x reference voltage
    Mul2 = 1,
    /// 4x reference voltage
    Mul4 = 2,
    /// 8x reference voltage (lowest sensitivity)
    Mul8 = 3,
}

impl ZeroWindowVolt {
    /// Converts enum value to 2-bit number
    pub const fn into_bits(self) -> u8 {
        self as u8
    }

    /// Generates enum value from 2-bit number
    ///
    /// # Arguments
    /// * `value` - Value in range 0-3 (2 bits)
    ///
    /// # Returns
    /// Corresponding ZeroWindowVolt value. Returns Mul1 for out-of-range values.
    pub const fn from_bits(value: u8) -> Self {
        match value {
            0 => ZeroWindowVolt::Mul1,
            1 => ZeroWindowVolt::Mul2,
            2 => ZeroWindowVolt::Mul4,
            3 => ZeroWindowVolt::Mul8,
            _ => ZeroWindowVolt::Mul1, // Default value
        }
    }
}

/// Soft clock setting command
///
/// # Builder Methods
///
/// This struct provides builder methods generated by the `bitfield-struct` crate:
/// - `new()` - Creates a new instance with default values
/// - `with_chip_addr(u8)` - Sets the chip address (2 bits)
/// - `with_internal_clock(bool)` - Enables internal clock operation
/// - `with_clock_div(ClockDiv)` - Sets clock division ratio
/// - `with_zero_window_volt(ZeroWindowVolt)` - Sets zero-cross detection voltage width
///
/// # Example
///
/// ```
/// use muses72323::commands::{SoftClock, ClockDiv, ZeroWindowVolt};
///
/// let cmd = SoftClock::new()
///     .with_chip_addr(0b10)
///     .with_internal_clock(true)
///     .with_clock_div(ClockDiv::Div32)
///     .with_zero_window_volt(ZeroWindowVolt::Mul4);
///
/// let raw: u16 = cmd.into();
/// ```
#[bitfield(u16)]
pub struct SoftClock {
    /// Chip address. Must match the state of ADR0, ADR1 (chip address selection pins).
    #[bits(2)]
    pub chip_addr: u8,
    /// Fixed to 0b0000011.
    #[bits(7, default = 0b0000011)]
    __: u8,
    /// Use internal clock operation.
    pub internal_clock: bool,
    /// Clock division ratio
    #[bits(3)]
    pub clock_div: ClockDiv,
    /// Zero-cross detection voltage width
    #[bits(2)]
    pub zero_window_volt: ZeroWindowVolt,
    /// Fixed to 0
    #[bits(1)]
    __: u8,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_volume_roundtrip() {
        // Set values to SetVolume
        let volume = SetVolume::new()
            .with_chip_addr(0b11)
            .with_channel(Channel::R)
            .with_is_soft_step(true)
            .with_volume(0b101010101);

        // Read as u16
        let raw_value: u16 = volume.into();

        // Calculate expected value
        // Bit layout: [volume:9][__:2][is_soft_step:1][channel:2][chip_addr:2]
        // chip_addr: 0b11 (bits 0-1)
        // channel: 0b01 (bits 2-3, Channel::R = 1)
        // is_soft_step: 0b1 (bit 4)
        // __: 0b00 (bits 5-6)
        // volume: 0b101010101 (bits 7-15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b101010101_00_1_01_11;

        assert_eq!(raw_value, expected);

        // Verify reverse conversion
        let decoded = SetVolume::from(raw_value);
        assert_eq!(decoded.chip_addr(), 0b11);
        assert_eq!(decoded.channel(), Channel::R);
        assert!(decoded.is_soft_step());
        assert_eq!(decoded.volume(), 0b101010101);
    }

    #[test]
    fn test_set_volume_all_fields() {
        // Test with maximum values for each field
        let volume = SetVolume::new()
            .with_chip_addr(0b11)      // 2-bit max value
            .with_channel(Channel::LorBoth)
            .with_is_soft_step(false)
            .with_volume(0b111111111);  // 9-bit max value

        let raw_value: u16 = volume.into();
        
        // Calculate expected value
        // Bit layout: [volume:9][__:2][is_soft_step:1][channel:2][chip_addr:2]
        // chip_addr: 0b11 (bits 0-1)
        // channel: 0b00 (bits 2-3, Channel::L = 0)
        // is_soft_step: 0b0 (bit 4)
        // __: 0b00 (bits 5-6)
        // volume: 0b111111111 (bits 7-15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b111111111_00_0_00_11;
        
        assert_eq!(raw_value, expected);
        
        let decoded = SetVolume::from(raw_value);

        assert_eq!(decoded.chip_addr(), 0b11);
        assert_eq!(decoded.channel(), Channel::LorBoth);
        assert!(!decoded.is_soft_step());
        assert_eq!(decoded.volume(), 0b111111111);
    }

    #[test]
    fn test_set_gain_roundtrip() {
        // Set values to SetGain
        let gain = SetGain::new()
            .with_chip_addr(0b10)
            .with_zero_cross_off(true)
            .with_r_gain(Gain::Gain15db)
            .with_l_gain(Gain::Gain9db)
            .with_l_r_cont(false);

        // Read as u16
        let raw_value: u16 = gain.into();

        // Calculate expected value
        // Bit layout: [l_r_cont:1][l_gain:3][r_gain:3][zero_cross_off:1][__:6][chip_addr:2]
        // chip_addr: 0b10 (bits 0-1)
        // __: 0b000010 (bits 2-7, デフォルト値)
        // zero_cross_off: 0b1 (bit 8)
        // r_gain: 0b101 (bits 9-11, Gain15db = 5)
        // l_gain: 0b011 (bits 12-14, Gain9db = 3)
        // l_r_cont: 0b0 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b0_011_101_1_000010_10;

        assert_eq!(raw_value, expected);

        // Verify reverse conversion
        let decoded = SetGain::from(raw_value);
        assert_eq!(decoded.chip_addr(), 0b10);
        assert!(decoded.zero_cross_off());
        assert_eq!(decoded.r_gain(), Gain::Gain15db);
        assert_eq!(decoded.l_gain(), Gain::Gain9db);
        assert!(!decoded.l_r_cont());
    }

    #[test]
    fn test_set_gain_default_fixed_bits() {
        // Verify that __ becomes 0b000010 with default value
        let gain = SetGain::new()
            .with_chip_addr(0b00)
            .with_zero_cross_off(false)
            .with_r_gain(Gain::Gain0)
            .with_l_gain(Gain::Gain0)
            .with_l_r_cont(false);

        let raw_value: u16 = gain.into();
        
        // Calculate expected value
        // Bit layout: [l_r_cont:1][l_gain:3][r_gain:3][zero_cross_off:1][__:6][chip_addr:2]
        // chip_addr: 0b00 (bits 0-1)
        // __: 0b000010 (bits 2-7, デフォルト値)
        // zero_cross_off: 0b0 (bit 8)
        // r_gain: 0b000 (bits 9-11, Gain0 = 0)
        // l_gain: 0b000 (bits 12-14, Gain0 = 0)
        // l_r_cont: 0b0 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b0_000_000_0_000010_00;
        
        assert_eq!(raw_value, expected);
    }

    #[test]
    fn test_set_gain_all_max_values() {
        // Test with maximum values for each field
        let gain = SetGain::new()
            .with_chip_addr(0b11)           // 2-bit max value
            .with_zero_cross_off(true)
            .with_r_gain(Gain::Gain21db)    // Maximum gain
            .with_l_gain(Gain::Gain21db)    // Maximum gain
            .with_l_r_cont(true);

        let raw_value: u16 = gain.into();
        
        // Calculate expected value
        // Bit layout: [l_r_cont:1][l_gain:3][r_gain:3][zero_cross_off:1][__:6][chip_addr:2]
        // chip_addr: 0b11 (bits 0-1)
        // __: 0b000010 (bits 2-7, デフォルト値)
        // zero_cross_off: 0b1 (bit 8)
        // r_gain: 0b111 (bits 9-11, Gain21db = 7)
        // l_gain: 0b111 (bits 12-14, Gain21db = 7)
        // l_r_cont: 0b1 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b1_111_111_1_000010_11;
        
        assert_eq!(raw_value, expected);
        
        let decoded = SetGain::from(raw_value);
        assert_eq!(decoded.chip_addr(), 0b11);
        assert!(decoded.zero_cross_off());
        assert_eq!(decoded.r_gain(), Gain::Gain21db);
        assert_eq!(decoded.l_gain(), Gain::Gain21db);
        assert!(decoded.l_r_cont());
    }

    #[test]
    fn test_soft_clock_roundtrip() {
        // Set values to SoftClock
        let soft_clock = SoftClock::new()
            .with_chip_addr(0b10)
            .with_internal_clock(true)
            .with_clock_div(ClockDiv::Div32)
            .with_zero_window_volt(ZeroWindowVolt::Mul4);

        // Read as u16
        let raw_value: u16 = soft_clock.into();

        // Calculate expected value
        // Bit layout: [__:1][zero_window_volt:2][clock_div:3][internal_clock:1][__:7][chip_addr:2]
        // chip_addr: 0b10 (bits 0-1)
        // __: 0b0000011 (bits 2-8, デフォルト値)
        // internal_clock: 0b1 (bit 9)
        // clock_div: 0b100 (bits 10-12, Div32 = 4)
        // zero_window_volt: 0b10 (bits 13-14, Mul4 = 2)
        // __: 0b0 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b0_10_100_1_0000011_10;

        assert_eq!(raw_value, expected);

        // Verify reverse conversion
        let decoded = SoftClock::from(raw_value);
        assert_eq!(decoded.chip_addr(), 0b10);
        assert!(decoded.internal_clock());
        assert_eq!(decoded.clock_div(), ClockDiv::Div32);
        assert_eq!(decoded.zero_window_volt(), ZeroWindowVolt::Mul4);
    }

    #[test]
    fn test_soft_clock_default_fixed_bits() {
        // Verify that __ becomes 0b0000011 with default value
        let soft_clock = SoftClock::new()
            .with_chip_addr(0b00)
            .with_internal_clock(false)
            .with_clock_div(ClockDiv::Div1)
            .with_zero_window_volt(ZeroWindowVolt::Mul1);

        let raw_value: u16 = soft_clock.into();
        
        // Calculate expected value
        // Bit layout: [__:1][zero_window_volt:2][clock_div:3][internal_clock:1][__:7][chip_addr:2]
        // chip_addr: 0b00 (bits 0-1)
        // __: 0b0000011 (bits 2-8, デフォルト値)
        // internal_clock: 0b0 (bit 9)
        // clock_div: 0b000 (bits 10-12, Div1 = 0)
        // zero_window_volt: 0b00 (bits 13-14, Mul1 = 0)
        // __: 0b0 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b0_00_000_0_0000011_00;
        
        assert_eq!(raw_value, expected);
    }

    #[test]
    fn test_soft_clock_all_max_values() {
        // Test with maximum values for each field
        let soft_clock = SoftClock::new()
            .with_chip_addr(0b11)                      // 2-bit max value
            .with_internal_clock(true)
            .with_clock_div(ClockDiv::Div256)          // Maximum division ratio
            .with_zero_window_volt(ZeroWindowVolt::Mul8); // Maximum voltage width

        let raw_value: u16 = soft_clock.into();
        
        // Calculate expected value
        // Bit layout: [__:1][zero_window_volt:2][clock_div:3][internal_clock:1][__:7][chip_addr:2]
        // chip_addr: 0b11 (bits 0-1)
        // __: 0b0000011 (bits 2-8, デフォルト値)
        // internal_clock: 0b1 (bit 9)
        // clock_div: 0b111 (bits 10-12, Div256 = 7)
        // zero_window_volt: 0b11 (bits 13-14, Mul8 = 3)
        // __: 0b0 (bit 15)
        #[allow(clippy::unusual_byte_groupings)]
        let expected: u16 = 0b0_11_111_1_0000011_11;
        
        assert_eq!(raw_value, expected);
        
        let decoded = SoftClock::from(raw_value);
        assert_eq!(decoded.chip_addr(), 0b11);
        assert!(decoded.internal_clock());
        assert_eq!(decoded.clock_div(), ClockDiv::Div256);
        assert_eq!(decoded.zero_window_volt(), ZeroWindowVolt::Mul8);
    }

    #[test]
    fn test_soft_clock_all_clock_divs() {
        // Test all ClockDiv values
        let clock_divs = [
            (ClockDiv::Div1, 0b000),
            (ClockDiv::Div4, 0b001),
            (ClockDiv::Div8, 0b010),
            (ClockDiv::Div16, 0b011),
            (ClockDiv::Div32, 0b100),
            (ClockDiv::Div64, 0b101),
            (ClockDiv::Div128, 0b110),
            (ClockDiv::Div256, 0b111),
        ];

        for (div, expected_bits) in clock_divs {
            let soft_clock = SoftClock::new()
                .with_chip_addr(0b00)
                .with_internal_clock(false)
                .with_clock_div(div)
                .with_zero_window_volt(ZeroWindowVolt::Mul1);

            let raw_value: u16 = soft_clock.into();
            let decoded = SoftClock::from(raw_value);
            assert_eq!(decoded.clock_div(), div);
            
            // Verify bit value
            let raw_value: u16 = soft_clock.into();
            let clock_div_bits = (raw_value >> 10) & 0b111;
            assert_eq!(clock_div_bits, expected_bits as u16);
        }
    }

    #[test]
    fn test_soft_clock_all_zero_window_volts() {
        // Test all ZeroWindowVolt values
        let zero_window_volts = [
            (ZeroWindowVolt::Mul1, 0b00),
            (ZeroWindowVolt::Mul2, 0b01),
            (ZeroWindowVolt::Mul4, 0b10),
            (ZeroWindowVolt::Mul8, 0b11),
        ];

        for (volt, expected_bits) in zero_window_volts {
            let soft_clock = SoftClock::new()
                .with_chip_addr(0b00)
                .with_internal_clock(false)
                .with_clock_div(ClockDiv::Div1)
                .with_zero_window_volt(volt);

            let raw_value: u16 = soft_clock.into();
            let decoded = SoftClock::from(raw_value);
            assert_eq!(decoded.zero_window_volt(), volt);
            
            // Verify bit value
            let raw_value: u16 = soft_clock.into();
            let zero_window_bits = (raw_value >> 13) & 0b11;
            assert_eq!(zero_window_bits, expected_bits as u16);
        }
    }

    #[test]
    fn test_soft_clock_internal_external_clock() {
        // Test switching between internal and external clock
        let internal = SoftClock::new()
            .with_chip_addr(0b01)
            .with_internal_clock(true)
            .with_clock_div(ClockDiv::Div1)
            .with_zero_window_volt(ZeroWindowVolt::Mul1);

        let external = SoftClock::new()
            .with_chip_addr(0b01)
            .with_internal_clock(false)
            .with_clock_div(ClockDiv::Div1)
            .with_zero_window_volt(ZeroWindowVolt::Mul1);

        let internal_raw: u16 = internal.into();
        let external_raw: u16 = external.into();

        // Verify that only the internal_clock bit (bit 9) differs
        assert_eq!(internal_raw ^ external_raw, 1 << 9);

        // Verify by decoding
        let internal_decoded = SoftClock::from(internal_raw);
        let external_decoded = SoftClock::from(external_raw);
        
        assert!(internal_decoded.internal_clock());
        assert!(!external_decoded.internal_clock());
    }

    // Type-safe Volume tests
    #[test]
    fn test_volume_value_valid_range() {
        // Test minimum value
        let min = VolumeValue::try_from(0).unwrap();
        assert_eq!(min.get(), 0);
        assert_eq!(min.to_hardware_value(), Volume::MAX_HW);

        // Test maximum value
        let max = VolumeValue::try_from(VolumeValue::MAX).unwrap();
        assert_eq!(max.get(), VolumeValue::MAX);
        assert_eq!(max.to_hardware_value(), Volume::MIN_HW);

        // Test middle value
        let mid = VolumeValue::try_from(223).unwrap();
        assert_eq!(mid.get(), 223);
        assert_eq!(mid.to_hardware_value(), Volume::MAX_HW - 223);
    }

    #[test]
    fn test_volume_value_invalid_range() {
        // Test values beyond maximum
        assert!(VolumeValue::try_from(VolumeValue::MAX + 1).is_err());
        assert!(VolumeValue::try_from(448).is_err());
        assert!(VolumeValue::try_from(500).is_err());
        assert!(VolumeValue::try_from(u16::MAX).is_err());
    }

    #[test]
    fn test_volume_value_from_hardware_value() {
        // Test minimum hardware value
        let min = VolumeValue::from_hardware_value(Volume::MIN_HW).unwrap();
        assert_eq!(min.get(), VolumeValue::MAX);

        // Test maximum hardware value
        let max = VolumeValue::from_hardware_value(Volume::MAX_HW).unwrap();
        assert_eq!(max.get(), 0);

        // Test middle hardware value
        let mid = VolumeValue::from_hardware_value(255).unwrap();
        assert_eq!(mid.get(), Volume::MAX_HW - 255);

        // Test invalid hardware values
        assert!(VolumeValue::from_hardware_value(0).is_err());
        assert!(VolumeValue::from_hardware_value(31).is_err());
        assert!(VolumeValue::from_hardware_value(Volume::MAX_HW + 1).is_err());
        assert!(VolumeValue::from_hardware_value(500).is_err());
    }

    #[test]
    fn test_volume_value_conversions() {
        // Test u16 conversion
        let vol = VolumeValue::try_from(100).unwrap();
        let as_u16: u16 = vol.into();
        assert_eq!(as_u16, 100);

        // Test roundtrip conversion
        let original = 250u16;
        let vol = VolumeValue::try_from(original).unwrap();
        let back: u16 = vol.into();
        assert_eq!(back, original);
    }

    #[test]
    fn test_volume_value_ordering() {
        let vol1 = VolumeValue::try_from(100).unwrap();
        let vol2 = VolumeValue::try_from(200).unwrap();
        let vol3 = VolumeValue::try_from(100).unwrap();

        assert!(vol1 < vol2);
        assert!(vol2 > vol1);
        assert_eq!(vol1, vol3);
        assert!(vol1 <= vol3);
        assert!(vol1 >= vol3);
    }

    #[test]
    fn test_volume_mute_variants() {
        // Test Mute0
        assert_eq!(Volume::Mute0.into_bits(), 0);
        assert!(Volume::Mute0.is_mute());

        // Test Mute511
        assert_eq!(Volume::Mute511.into_bits(), 0b111111111);
        assert!(Volume::Mute511.is_mute());

        // Test Volume variant is not mute
        let vol = VolumeValue::try_from(100).unwrap();
        assert!(!Volume::Volume(vol).is_mute());
    }

    #[test]
    fn test_volume_from_hardware_value() {
        // Test Mute0
        let mute0 = Volume::try_from(0).unwrap();
        assert_eq!(mute0, Volume::Mute0);
        assert!(mute0.is_mute());

        // Test Mute511
        let mute511 = Volume::try_from(511).unwrap();
        assert_eq!(mute511, Volume::Mute511);
        assert!(mute511.is_mute());

        // Test minimum hardware value (32) → creates VolumeValue(447) → converts back to 32
        let min_hw_vol = Volume::try_from(Volume::MIN_HW).unwrap();
        assert!(!min_hw_vol.is_mute());
        assert_eq!(min_hw_vol.into_bits(), Volume::MIN_HW);

        // Test maximum hardware value (479) → creates VolumeValue(0) → converts back to 479
        let max_hw_vol = Volume::try_from(Volume::MAX_HW).unwrap();
        assert!(!max_hw_vol.is_mute());
        assert_eq!(max_hw_vol.into_bits(), Volume::MAX_HW);

        // Test middle volume - should roundtrip
        let mid_vol = Volume::try_from(255).unwrap();
        assert!(!mid_vol.is_mute());
        assert_eq!(mid_vol.into_bits(), 255);
    }

    #[test]
    fn test_volume_invalid_hardware_values() {
        // Test invalid values between 1-31
        for i in 1..Volume::MIN_HW {
            assert!(Volume::try_from(i).is_err(), "Value {} should be invalid", i);
        }

        // Test invalid values between 480-510
        for i in (Volume::MAX_HW + 1)..511 {
            assert!(Volume::try_from(i).is_err(), "Value {} should be invalid", i);
        }
    }

    #[test]
    fn test_volume_roundtrip_conversion() {
        // Test Mute0 roundtrip
        let mute0 = Volume::Mute0;
        let bits = mute0.into_bits();
        let back = Volume::try_from(bits).unwrap();
        assert_eq!(back, mute0);

        // Test Mute511 roundtrip
        let mute511 = Volume::Mute511;
        let bits = mute511.into_bits();
        let back = Volume::try_from(bits).unwrap();
        assert_eq!(back, mute511);

        // Test Volume variant roundtrip
        let vol_value = VolumeValue::try_from(200).unwrap();
        let vol = Volume::Volume(vol_value);
        let bits = vol.into_bits();
        let back = Volume::try_from(bits).unwrap();
        assert_eq!(back.into_bits(), vol.into_bits());
    }

    #[test]
    fn test_set_volume_with_safe_volume() {
        // Test with VolumeValue
        let vol_value = VolumeValue::try_from(100).unwrap();
        let cmd = SetVolume::new()
            .with_chip_addr(0b10)
            .with_channel(Channel::LorBoth)
            .with_is_soft_step(true)
            .safe_with_volume(Volume::Volume(vol_value));

        assert_eq!(cmd.volume(), vol_value.to_hardware_value());
        let retrieved = cmd.volume_value().unwrap();
        assert_eq!(retrieved.into_bits(), Volume::Volume(vol_value).into_bits());

        // Test with Mute0
        let mute_cmd = SetVolume::new()
            .with_chip_addr(0b10)
            .with_channel(Channel::R)
            .with_is_soft_step(false)
            .safe_with_volume(Volume::Mute0);

        assert_eq!(mute_cmd.volume(), 0);
        let retrieved_mute = mute_cmd.volume_value().unwrap();
        assert_eq!(retrieved_mute, Volume::Mute0);
        assert!(retrieved_mute.is_mute());

        // Test with Mute511
        let mute511_cmd = SetVolume::new()
            .with_chip_addr(0b11)
            .with_channel(Channel::LorBoth)
            .with_is_soft_step(true)
            .safe_with_volume(Volume::Mute511);

        assert_eq!(mute511_cmd.volume(), 511);
        let retrieved_mute511 = mute511_cmd.volume_value().unwrap();
        assert_eq!(retrieved_mute511, Volume::Mute511);
        assert!(retrieved_mute511.is_mute());
    }

    #[test]
    fn test_set_volume_boundary_values() {
        // Test minimum volume (0 → 479)
        let min_vol = VolumeValue::try_from(0).unwrap();
        let cmd = SetVolume::new().safe_with_volume(Volume::Volume(min_vol));
        assert_eq!(cmd.volume(), Volume::MAX_HW);

        // Test maximum volume (447 → 32)
        let max_vol = VolumeValue::try_from(VolumeValue::MAX).unwrap();
        let cmd = SetVolume::new().safe_with_volume(Volume::Volume(max_vol));
        assert_eq!(cmd.volume(), Volume::MIN_HW);
    }

    #[test]
    fn test_set_volume_complete_roundtrip() {
        // Create command with type-safe volume
        let vol_value = VolumeValue::try_from(300).unwrap();
        let original_cmd = SetVolume::new()
            .with_chip_addr(0b11)
            .with_channel(Channel::R)
            .with_is_soft_step(true)
            .safe_with_volume(Volume::Volume(vol_value));

        // Convert to u16
        let raw: u16 = original_cmd.into();

        // Convert back to SetVolume
        let decoded_cmd = SetVolume::from(raw);

        // Verify all fields
        assert_eq!(decoded_cmd.chip_addr(), 0b11);
        assert_eq!(decoded_cmd.channel(), Channel::R);
        assert!(decoded_cmd.is_soft_step());
        assert_eq!(decoded_cmd.volume(), vol_value.to_hardware_value());

        // Verify volume can be retrieved as Volume type
        let retrieved_vol = decoded_cmd.volume_value().unwrap();
        assert_eq!(retrieved_vol.into_bits(), Volume::Volume(vol_value).into_bits());
        assert!(!retrieved_vol.is_mute());
    }

    #[test]
    fn test_volume_value_error_display() {
        let err = VolumeValue::try_from(500).unwrap_err();
        let msg = format!("{}", err);
        assert!(msg.contains("Invalid volume level value"));
        assert!(msg.contains("500"));
        assert!(msg.contains("0-447"));
    }

    #[test]
    fn test_volume_error_display() {
        let err = Volume::try_from(15).unwrap_err();
        let msg = format!("{}", err);
        assert!(msg.contains("Invalid volume value"));
        assert!(msg.contains("15"));
        assert!(msg.contains("32"));
        assert!(msg.contains("479"));
    }

    #[test]
    fn test_volume_all_valid_hardware_values() {
        // Test all valid hardware values in the range - should roundtrip
        for hw_val in Volume::MIN_HW..=Volume::MAX_HW {
            let vol = Volume::try_from(hw_val).unwrap();
            assert_eq!(vol.into_bits(), hw_val);
            assert!(!vol.is_mute());
        }
    }

    #[test]
    fn test_volume_value_all_valid_values() {
        // Test all valid VolumeValue values
        for val in 0..=VolumeValue::MAX {
            let vol_value = VolumeValue::try_from(val).unwrap();
            assert_eq!(vol_value.get(), val);
            assert_eq!(vol_value.to_hardware_value(), Volume::MAX_HW - val);
            
            // Verify roundtrip through hardware value
            let from_hw = VolumeValue::from_hardware_value(vol_value.to_hardware_value()).unwrap();
            assert_eq!(from_hw.get(), val);
        }
    }

    #[test]
    fn test_volume_from_trait() {
        // Test From<Volume> for u16 trait implementation
        // VolumeValue(100) -> hardware value = 479 - 100 = 379
        let vol_value = VolumeValue::try_from(100).unwrap();
        let volume = Volume::Volume(vol_value);
        let as_u16: u16 = volume.into();
        assert_eq!(as_u16, 379);

        // Test with Mute0
        let mute0_u16: u16 = Volume::Mute0.into();
        assert_eq!(mute0_u16, 0);

        // Test with Mute511
        let mute511_u16: u16 = Volume::Mute511.into();
        assert_eq!(mute511_u16, 511);
    }

    #[test]
    fn test_channel_from_bits_invalid() {
        // Test invalid channel values (should default to LorBoth)
        assert_eq!(Channel::from_bits(2), Channel::LorBoth);
        assert_eq!(Channel::from_bits(3), Channel::LorBoth);
        assert_eq!(Channel::from_bits(255), Channel::LorBoth);
    }

    #[test]
    fn test_gain_from_bits_all_values() {
        // Test all valid Gain values
        assert_eq!(Gain::from_bits(0), Gain::Gain0);
        assert_eq!(Gain::from_bits(1), Gain::Gain3db);
        assert_eq!(Gain::from_bits(2), Gain::Gain6db);
        assert_eq!(Gain::from_bits(3), Gain::Gain9db);
        assert_eq!(Gain::from_bits(4), Gain::Gain12db);
        assert_eq!(Gain::from_bits(5), Gain::Gain15db);
        assert_eq!(Gain::from_bits(6), Gain::Gain18db);
        assert_eq!(Gain::from_bits(7), Gain::Gain21db);

        // Test invalid values (should default to Gain0)
        assert_eq!(Gain::from_bits(8), Gain::Gain0);
        assert_eq!(Gain::from_bits(255), Gain::Gain0);
    }

    #[test]
    fn test_clock_div_from_bits_invalid() {
        // Test invalid ClockDiv values (should default to Div1)
        assert_eq!(ClockDiv::from_bits(8), ClockDiv::Div1);
        assert_eq!(ClockDiv::from_bits(255), ClockDiv::Div1);
    }

    #[test]
    fn test_zero_window_volt_from_bits_invalid() {
        // Test invalid ZeroWindowVolt values (should default to Mul1)
        assert_eq!(ZeroWindowVolt::from_bits(4), ZeroWindowVolt::Mul1);
        assert_eq!(ZeroWindowVolt::from_bits(255), ZeroWindowVolt::Mul1);
    }
}

# muses72323

[![Crates.io](https://img.shields.io/crates/v/muses72323.svg)](https://crates.io/crates/muses72323)
[![Documentation](https://docs.rs/muses72323/badge.svg)](https://docs.rs/muses72323)
[![License](https://img.shields.io/crates/l/muses72323.svg)](https://github.com/ruimo/muses72323/blob/main/LICENSE)

A Rust driver library for the MUSES72323 electronic volume controller IC.

## Overview

The MUSES72323 is a high-quality 2-channel electronic volume controller IC manufactured by Nisshinbo Micro Devices Inc. This crate provides type-safe, zero-cost abstractions for controlling the MUSES72323 via its serial interface.

### Key Features

- **Volume Control**: 0dB to -111.75dB in 0.25dB steps (512 steps)
- **Gain Control**: 0dB to +21dB in +3dB steps (8 levels)
- **Soft Step Function**: Reduces zipper noise during volume changes
- **Zero-Cross Detection**: Minimizes pop noise when changing volume
- **Independent or Linked L/R Control**: Control channels separately or together
- **Type-Safe API**: Compile-time guarantees for valid configurations
- **No-std Compatible**: Works in embedded environments

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
muses72323 = "0.1.0"
```

## Usage

### Basic Volume Control

```rust
use muses72323::commands::{SetVolume, Channel};

// Set volume to -20dB (80 steps of 0.25dB)
let volume_cmd = SetVolume::new()
    .with_chip_addr(0b00)           // Chip address (ADR0, ADR1 pins)
    .with_channel(Channel::LorBoth) // Control left or both channels
    .with_is_soft_step(true)        // Enable soft step to reduce zipper noise
    .with_volume(80);               // 80 * 0.25dB = -20dB

// Convert to u16 for transmission
let data: u16 = volume_cmd.into();
// Send `data` to MUSES72323 via your serial interface
```

### Gain Control

```rust
use muses72323::commands::{SetGain, Gain};

// Set gain to +12dB for both channels
let gain_cmd = SetGain::new()
    .with_chip_addr(0b00)
    .with_l_gain(Gain::Gain12db)    // Left channel: +12dB
    .with_r_gain(Gain::Gain12db)    // Right channel: +12dB
    .with_l_r_cont(true)            // Link L/R channels
    .with_zero_cross_off(false);    // Enable zero-cross detection

let data: u16 = gain_cmd.into();
```

### Clock Configuration

```rust
use muses72323::commands::{SoftClock, ClockDiv, ZeroWindowVolt};

// Configure soft clock with internal clock and 1/32 division
let clock_cmd = SoftClock::new()
    .with_chip_addr(0b00)
    .with_internal_clock(true)              // Use internal clock
    .with_clock_div(ClockDiv::Div32)        // 1/32 clock division
    .with_zero_window_volt(ZeroWindowVolt::Mul4); // Zero-cross detection window

let data: u16 = clock_cmd.into();
```

## Command Reference

### SetVolume

Controls the volume level for each channel.

- **Volume Range**: 0 to 511 (0dB to -111.75dB in 0.25dB steps)
  - 0 = 0dB (maximum volume)
  - 80 = -20dB
  - 511 = -111.75dB (minimum volume)
- **Soft Step**: Gradually changes volume to reduce zipper noise
- **Channel**: Control left, right, or both channels (when L/R linked)

### SetGain

Controls the gain level for each channel.

Available gain levels:
- `Gain0` = 0dB
- `Gain3db` = +3dB
- `Gain6db` = +6dB
- `Gain9db` = +9dB
- `Gain12db` = +12dB
- `Gain15db` = +15dB
- `Gain18db` = +18dB
- `Gain21db` = +21dB

Options:
- **L/R Control**: Link channels for synchronized control
- **Zero-Cross Detection**: Enable/disable pop noise reduction

### SoftClock

Configures the soft step clock and zero-cross detection.

- **Clock Source**: Internal or external clock
- **Clock Division**: 1/1, 1/4, 1/8, 1/16, 1/32, 1/64, 1/128, 1/256
- **Zero-Cross Window**: Sensitivity of zero-cross detection (1x, 2x, 4x, 8x)

## Hardware Interface

The MUSES72323 uses a 3-wire serial interface:

- **DATA**: Serial data input
- **CLOCK**: Serial clock input
- **LATCH**: Data latch signal

Typical transmission sequence:
1. Set LATCH low
2. Send 16-bit command data (MSB first) on DATA line, clocked by CLOCK
3. Set LATCH high to latch the data

## Examples

### Complete Volume Control System

```rust
use muses72323::commands::{SetVolume, SetGain, SoftClock, Channel, Gain, ClockDiv, ZeroWindowVolt};

// Initialize with soft clock configuration
let clock_cmd = SoftClock::new()
    .with_chip_addr(0b00)
    .with_internal_clock(true)
    .with_clock_div(ClockDiv::Div32)
    .with_zero_window_volt(ZeroWindowVolt::Mul4);
send_to_muses(clock_cmd.into());

// Set initial gain
let gain_cmd = SetGain::new()
    .with_chip_addr(0b00)
    .with_l_gain(Gain::Gain0)
    .with_r_gain(Gain::Gain0)
    .with_l_r_cont(true)
    .with_zero_cross_off(false);
send_to_muses(gain_cmd.into());

// Set volume with soft step
let volume_cmd = SetVolume::new()
    .with_chip_addr(0b00)
    .with_channel(Channel::LorBoth)
    .with_is_soft_step(true)
    .with_volume(100); // -25dB
send_to_muses(volume_cmd.into());

fn send_to_muses(data: u16) {
    // Implement your serial transmission here
    // Example for embedded systems:
    // - Set LATCH low
    // - Send 16 bits MSB first
    // - Set LATCH high
}
```

### Volume Fade

```rust
use muses72323::commands::{SetVolume, Channel};

fn fade_volume(from: u16, to: u16, chip_addr: u8) {
    let step = if from < to { 1 } else { -1 };
    let mut current = from as i16;
    let target = to as i16;
    
    while current != target {
        let cmd = SetVolume::new()
            .with_chip_addr(chip_addr)
            .with_channel(Channel::LorBoth)
            .with_is_soft_step(true)
            .with_volume(current as u16);
        
        send_to_muses(cmd.into());
        current += step;
        
        // Add delay between steps if needed
        delay_ms(10);
    }
}
```

## Technical Details

### Bit Field Layout

All commands are 16-bit values with specific bit layouts:

**SetVolume** (Command ID: 0b00):
```
[15:7] Volume (9 bits)
[6:5]  Reserved (0b00)
[4]    Soft Step Enable
[3:2]  Channel Select
[1:0]  Chip Address
```

**SetGain** (Command ID: 0b000010):
```
[15]   L/R Control
[14:12] L Gain (3 bits)
[11:9]  R Gain (3 bits)
[8]    Zero-Cross Off
[7:2]  Command ID (0b000010)
[1:0]  Chip Address
```

**SoftClock** (Command ID: 0b0000011):
```
[15]   Reserved (0)
[14:13] Zero Window Voltage (2 bits)
[12:10] Clock Division (3 bits)
[9]    Internal Clock Enable
[8:2]  Command ID (0b0000011)
[1:0]  Chip Address
```

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## References

- [MUSES72323 Datasheet](https://www.nisshinbo-microdevices.co.jp/ja/pdf/datasheet/MUSES72323_J.pdf)
- [Repository](https://github.com/ruimo/muses72323)
- [Documentation](https://docs.rs/muses72323)

## Author

Shisei Hanai <ruimo.uno@gmail.com>
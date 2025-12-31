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

Please see [Documentation](https://docs.rs/muses72323/latest/muses72323/) for details.

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

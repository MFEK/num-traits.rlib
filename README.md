# num-traits

[![crate](https://img.shields.io/crates/v/num-traits.svg)](https://crates.io/crates/num-traits)
[![documentation](https://docs.rs/num-traits/badge.svg)](https://docs.rs/num-traits)
[![minimum rustc 1.8](https://img.shields.io/badge/rustc-1.8+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)
[![build status](https://github.com/rust-num/num-traits/workflows/master/badge.svg)](https://github.com/rust-num/num-traits/actions)

Numeric traits for generic mathematics in Rust.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
num-traits = "0.2"
```

## Features

This crate can be used without the standard library (`#![no_std]`) by disabling
the default `std` feature. Use this in `Cargo.toml`:

```toml
[dependencies.num-traits]
version = "0.2"
default-features = false
# features = ["libm"]    # <--- Uncomment if you wish to use `Float` and `Real` without `std`
```

The `Float` and `Real` traits are only available when either `std` or `libm` is enabled.  
The `libm` feature is only available with Rust 1.31 and later ([see PR #99](https://github.com/rust-num/num-traits/pull/99)).

The `FloatCore` trait is always available.  `MulAdd` and `MulAddAssign` for `f32`
and `f64` also require `std` or `libm`, as do implementations of signed and floating-
point exponents in `Pow`.

Implementations for `i128` and `u128` are only available with Rust 1.26 and
later.  The build script automatically detects this, but you can make it
mandatory by enabling the `i128` crate feature.

The `const_conversion` feature makes it possible to perform `ToPrimitive`
conversions in `const` context (e.g.:
```
const FORTY_TWO: u64 = 42;
const FOO: u8 = FORTY_TWO.to_u8().unwrap();
```
Note that `unwrap()` in `const` context **does not panic**, but instead, *halts
compilation*, thereby ensuring validity at compile-time instead of 
runtime.

As of the time of this writing, the `const_trait_impl` feature in current
Rust (v1.56) is not yet stable.  When it does appear in stable Rust, `num-traits`
is set up to enable it automatically if it is stable in your compiler version.

If you wish to use this feature before then, set your project to a recent nightly 
version of the Rust compiler and enable the `const_conversion` feature by adding 
the following to the `[dependencies]`section of your `Cargo.toml` file:
```toml
# Cargo.toml
[dependencies]
# ... other dependencies your crate may have
num-traits = { version = "0.2.15", features = ["const_conversion"] }
```

## Releases

Release notes are available in [RELEASES.md](RELEASES.md).

## Compatibility

The `num-traits` crate is tested for rustc 1.8 and greater.

## License

Licensed under either of

 * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
 * [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

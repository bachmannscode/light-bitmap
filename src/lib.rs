//! A minimal, fixed-size bitmap library written in pure Rust.  
//! `no_std`, no heap / `alloc`, no `unsafe` — just `core`.
//!
//! Designed for use in embedded and resource-constrained environments.
//!
//! [`BitMap`] is the main struct in this library. Its [features](#features)
//! are listed below.
//!
//! # Examples
//! ```
//! use light_bitmap::{bucket_count, BitMap};
//!
//! const BIT_COUNT: usize = 10;
//! let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
//! assert_eq!(bitmap.popcount(), 0);
//! assert!(!bitmap.is_set(3));
//! bitmap.set(3);
//! assert!(bitmap.is_set(3));
//! assert_eq!(bitmap.popcount(), 1);
//! ```
//!
//! # Use Cases
//!
//! - Embedded development
//! - Applications that need a compact, stack-only bitmap with no dynamic allocation
//! - Timing-sensitive systems where allocation unpredictability must be avoided
//! - Does not support SIMD or parallel execution, so it's not ideal for cases
//!   where performance needs to be fully maxed out
//!
//! # Features
//!
//! - `#![no_std]` compatible
//! - Bit-level operations on a fixed number of bits
//! - No heap allocations (stack-only)
//! - Const-generic API: `BitMap<const BIT_COUNT, const BUCKET_COUNT>`
//! - Efficient iteration over all, set or unset bits:
//!   - `iter()` (all bits as bools)
//!   - `iter_ones()` (indices of set bits)
//!   - `iter_zeros()` (indices of unset bits)
//! - Support for bitwise ops:
//!   - `&`, `|`, `^`, `!`
//!   - `<<`, `>>`
//!   - `&=`, `|=`, `^=`, `<<=`, `>>=`
//! - Range operations: `set_range`, `unset_range`
//! - Logical operations: `popcount`, `first_set_bit`
//! - Rotation support: `rotate_left`, `rotate_right`

#![deny(missing_docs)]
#![forbid(unsafe_code)]
#![no_std]

mod bitmap;
#[cfg(test)]
mod tests;

pub use bitmap::{BitMap, BitMapIter, IterOnes, IterZeros, bucket_count};

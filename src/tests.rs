use super::*;
use bitmap::{compile_assert_const_params, ones_mask, runtime_assert_const_params};
use core::array::from_fn;
use core::fmt::{self, Write};

#[test]
fn test_bucket_count_runtime() {
    assert_eq!(bucket_count(8), 1);
    assert_eq!(bucket_count(9), 2);
    assert_eq!(bucket_count(16), 2);
    assert_eq!(bucket_count(17), 3);
    assert_eq!(bucket_count(24), 3);
    assert_eq!(bucket_count(25), 4);
    assert_eq!(bucket_count(33), 5);
    assert_eq!(bucket_count(100), 13);
}

#[test]
fn test_new() {
    macro_rules! test_new_by_bit_count {
                ($($bit_count:expr),+ $(,)?) => {
                    $(
                        {
                            const BIT_COUNT: usize = $bit_count;
                            let bitmap = BitMap::<BIT_COUNT, {bucket_count(BIT_COUNT)}>::new();
                            let mut bm_iter = bitmap.iter();
                            let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
                            let expected = [false; BIT_COUNT];
                            assert_eq!(actual, expected, "Failed for BIT_COUNT = {}", BIT_COUNT);
                        }
                    )+
                };
            }

    test_new_by_bit_count!(1, 17, 31, 32, 33, 45, 111, 127, 128, 129, 45342);
}

#[test]
fn test_default() {
    macro_rules! test_default_by_bit_count {
                ($($bit_count:expr),+ $(,)?) => {
                    $(
                        {
                            const BIT_COUNT: usize = $bit_count;
                            let bitmap = BitMap::<BIT_COUNT, {bucket_count(BIT_COUNT)}>::default();
                            let mut bm_iter = bitmap.iter();
                            let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
                            let expected = [false; BIT_COUNT];
                            assert_eq!(actual, expected, "Failed for BIT_COUNT = {}", BIT_COUNT);
                        }
                    )+
                };
            }

    test_default_by_bit_count!(1, 17, 31, 32, 33, 45, 111, 127, 128, 129, 45342);
}

#[test]
fn test_with_all_set() {
    macro_rules! test_with_all_set_by_bit_count {
            ($($bit_count:expr),+ $(,)?) => {
                $(
                    {
                        const BIT_COUNT: usize = $bit_count;
                        let bitmap = BitMap::<BIT_COUNT, {bucket_count(BIT_COUNT)}>::with_all_set();
                        let mut bm_iter = bitmap.iter();
                        let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
                        let expected = [true; BIT_COUNT];
                        assert_eq!(actual, expected, "Failed for BIT_COUNT = {}", BIT_COUNT);
                    }
                )+
            };
        }

    test_with_all_set_by_bit_count!(1, 7, 8, 9, 17, 31, 32, 33, 45, 111, 127, 128, 129, 45342);
}

#[test]
fn test_const_empty() {
    const BIT_COUNT: usize = 19;
    let bitmap = BitMap::<19, { bucket_count(BIT_COUNT) }>::const_empty();
    let mut bitmap_iter = bitmap.iter();
    assert_eq!([false; BIT_COUNT], from_fn(|_| bitmap_iter.next().unwrap()));
    assert_eq!(bitmap.popcount(), 0);
}

#[test]
fn test_const_full() {
    const BIT_COUNT: usize = 19;
    let bitmap = BitMap::<19, { bucket_count(BIT_COUNT) }>::const_full();
    let mut bitmap_iter = bitmap.iter();
    assert_eq!([true; BIT_COUNT], from_fn(|_| bitmap_iter.next().unwrap()));
    assert_eq!(bitmap.popcount(), 19);
}

#[test]
fn test_cover_compile_assert() {
    compile_assert_const_params(45, bucket_count(45));
}

#[test]
#[should_panic(expected = "assertion `left != right` failed: BIT_COUNT must be greater than zero.")]
fn test_runtime_assert_zero_bits() {
    runtime_assert_const_params(0, bucket_count(45));
}

#[test]
#[should_panic(
    expected = "assertion `left == right` failed: BUCKET_COUNT must match bucket_count(BIT_COUNT)."
)]
fn test_runtime_assert_bit_bucket_mismatch() {
    runtime_assert_const_params(45, 1);
}

#[test]
fn test_ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/zero_length_empty.rs");
    t.compile_fail("tests/ui/bits_buckets_mismatch_empty.rs");
    t.compile_fail("tests/ui/zero_length_full.rs");
    t.compile_fail("tests/ui/bits_buckets_mismatch_full.rs")
}

#[test]
fn test_from_slice() {
    const BIT_COUNT: usize = 17;
    let input = [
        true, false, true, false, false, true, false, true, // 0..8
        true, false, true, false, true, true, false, true, // 8..16
        true, // 16
    ];

    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&input);
    let mut iter = bitmap.iter();
    let roundtripped: [bool; BIT_COUNT] = from_fn(|_| iter.next().unwrap());

    assert_eq!(roundtripped, input);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_from_slice_wrong_length() {
    const BIT_COUNT: usize = 35;
    let invalid_input = [true; BIT_COUNT + 1];
    let _ = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&invalid_input);
}

#[test]
fn test_from_iter_and_fromiterator() {
    const BIT_COUNT: usize = 10;
    let input = [
        true, false, true, false, false, true, true, true, false, true,
    ];

    let from_iter: BitMap<BIT_COUNT, { bucket_count(BIT_COUNT) }> = input.into_iter().collect();

    let expected = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&input);
    assert_eq!(from_iter, expected);
}

#[test]
#[should_panic(expected = "yielded more than")]
fn test_from_iter_too_many() {
    const BIT_COUNT: usize = 10;
    let input = [true; 11];
    let _: BitMap<BIT_COUNT, { bucket_count(BIT_COUNT) }> = input.into_iter().collect();
}

#[test]
#[should_panic(expected = "yielded fewer than")]
fn test_from_iter_too_few() {
    const BIT_COUNT: usize = 10;
    let input = [true; 9];
    let _: BitMap<BIT_COUNT, { bucket_count(BIT_COUNT) }> = input.into_iter().collect();
}

#[test]
fn test_from_ones_iter() {
    const BIT_COUNT: usize = 10;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_ones_iter([0, 2, 5, 7, 9]);

    let mut iter = bitmap.iter();
    let actual = from_fn(|_| iter.next().unwrap());

    assert_eq!(
        actual,
        [
            true, false, true, false, false, true, false, true, false, true
        ]
    );
}

#[test]
#[should_panic(expected = "Bit index 10 out of bounds")]
fn test_from_ones_iter_out_of_bounds() {
    const BIT_COUNT: usize = 10;
    let _ = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_ones_iter([0, 2, 10]);
}

#[test]
fn test_iter() {
    const BIT_COUNT: usize = 10;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, true, false, true, false, true,
    ]);

    let mut iter = bitmap.iter();
    let all = from_fn(|_| iter.next().unwrap());
    assert_eq!(iter.next(), None);
    assert_eq!(
        all,
        [
            true, false, true, false, false, true, false, true, false, true
        ]
    );

    let mut into_iter = (&bitmap).into_iter();
    let all_into = from_fn(|_| into_iter.next().unwrap());
    assert_eq!(into_iter.next(), None);
    assert_eq!(
        all_into,
        [
            true, false, true, false, false, true, false, true, false, true
        ]
    );

    let mut ones_iter = bitmap.iter_ones();
    let ones = from_fn(|_| ones_iter.next().unwrap());
    assert_eq!(ones_iter.next(), None);
    assert_eq!(ones, [0, 2, 5, 7, 9]);

    let mut zeros_iter = bitmap.iter_zeros();
    let zeros = from_fn(|_| zeros_iter.next().unwrap());
    assert_eq!(zeros_iter.next(), None);
    assert_eq!(zeros, [1, 3, 4, 6, 8]);
}

#[test]
fn test_fused_iter() {
    const BIT_COUNT: usize = 10;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, true, false, true, false, true,
    ]);

    let mut iter = bitmap.iter();
    for _ in 0..BIT_COUNT {
        assert!(iter.next().is_some());
    }
    for _ in 0..30 {
        assert_eq!(iter.next(), None);
    }

    let mut ones_iter = bitmap.iter_ones();
    for _ in 0..bitmap.popcount() {
        assert!(ones_iter.next().is_some());
    }
    for _ in 0..30 {
        assert_eq!(ones_iter.next(), None);
    }

    let mut zeros_iter = bitmap.iter_zeros();
    for _ in 0..(BIT_COUNT - bitmap.popcount()) {
        assert!(zeros_iter.next().is_some());
    }
    for _ in 0..30 {
        assert_eq!(zeros_iter.next(), None);
    }
}

#[test]
fn test_unused_bit_iter() {
    const BIT_COUNT: usize = 1;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    bitmap.0[0] |= 1 << 1;
    let mut iter = bitmap.iter_ones();
    assert_eq!(iter.next(), None);
}

#[test]
fn test_set_and_unset() {
    const BIT_COUNT: usize = 35;
    const BUCKET_COUNT: usize = bucket_count(BIT_COUNT);
    let mut bitmap = BitMap::<BIT_COUNT, BUCKET_COUNT>::new();

    for idx in 0..BIT_COUNT {
        // Set it
        bitmap.set(idx);
        assert!(bitmap.is_set(idx), "Bit {} should be set", idx);

        // Unset it again
        bitmap.unset(idx);
        assert!(!bitmap.is_set(idx), "Bit {} should be unset", idx);
    }
}

#[test]
#[should_panic(expected = "Bit index 35 out of bounds")]
fn test_set_out_of_bounds() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    bitmap.set(BIT_COUNT); // one past the end
}

#[test]
fn test_ones_mask() {
    assert_eq!(ones_mask(0, 1), 0b00000001);
    assert_eq!(ones_mask(0, 2), 0b00000011);
    assert_eq!(ones_mask(0, 3), 0b00000111);
    assert_eq!(ones_mask(0, 4), 0b00001111);
    assert_eq!(ones_mask(0, 5), 0b00011111);
    assert_eq!(ones_mask(0, 6), 0b00111111);
    assert_eq!(ones_mask(0, 7), 0b01111111);
    assert_eq!(ones_mask(0, 8), 0b11111111);

    assert_eq!(ones_mask(2, 1), 0b00000100);
    assert_eq!(ones_mask(2, 2), 0b00001100);
    assert_eq!(ones_mask(2, 3), 0b00011100);
    assert_eq!(ones_mask(2, 4), 0b00111100);
    assert_eq!(ones_mask(2, 5), 0b01111100);
    assert_eq!(ones_mask(2, 6), 0b11111100);
    assert_eq!(ones_mask(2, 7), 0b11111100);
}

#[test]
fn test_set_range() {
    const BIT_COUNT: usize = 19;
    let original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    // over multiple buckets
    let mut bitmap = original;
    bitmap.set_range(3..17); // should set bits 3 through 16
    let expected = from_fn(|i| (3..17).contains(&i));
    let mut bm_iter = bitmap.iter();
    let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
    assert_eq!(actual, expected);

    // within one bucket
    let mut bitmap = original;
    bitmap.set_range(2..8); // should set bits 2 through 7
    let expected = from_fn(|i| (2..8).contains(&i));
    let mut bm_iter = bitmap.iter();
    let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
    assert_eq!(actual, expected);
}

#[test]
fn test_set_empty_range() {
    const BIT_COUNT: usize = 8;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set_range(5..5); // empty range
    let expected = [false; BIT_COUNT];
    let mut bm_iter = bitmap.iter();
    let actual = from_fn(|_| bm_iter.next().unwrap());

    assert_eq!(actual, expected);
}

#[test]
#[should_panic(expected = "Range end")]
fn test_set_end_range_out_of_bounds() {
    const BIT_COUNT: usize = 8;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set_range(2..BIT_COUNT + 1); // out-of-bounds end
}

#[test]
#[should_panic(expected = "Range start")]
fn test_set_start_range_out_of_bounds() {
    const BIT_COUNT: usize = 8;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set_range(BIT_COUNT..BIT_COUNT); // start too large
}

#[test]
fn test_unset_range() {
    const BIT_COUNT: usize = 19;
    let original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    // over multiple buckets
    let mut bitmap = original;
    bitmap.unset_range(3..17); // should unset bits 3 through 16
    let expected = from_fn(|i| !(3..17).contains(&i));
    let mut bm_iter = bitmap.iter();
    let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
    assert_eq!(actual, expected);

    // within one bucket
    let mut bitmap = original;
    bitmap.unset_range(2..8); // should unset bits 2 through 7
    let expected = from_fn(|i| !(2..8).contains(&i));
    let mut bm_iter = bitmap.iter();
    let actual: [bool; BIT_COUNT] = from_fn(|_| bm_iter.next().unwrap());
    assert_eq!(actual, expected);
}

#[test]
fn test_unset_empty_range() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    bitmap.unset_range(5..5); // empty range, should do nothing
    let expected = [true; BIT_COUNT];
    let mut bm_iter = bitmap.iter();
    let actual = from_fn(|_| bm_iter.next().unwrap());

    assert_eq!(actual, expected);
}

#[test]
#[should_panic(expected = "Range end")]
fn test_unset_end_range_out_of_bounds() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    bitmap.unset_range(2..BIT_COUNT + 1);
}

#[test]
#[should_panic(expected = "Range start")]
fn test_unset_start_range_out_of_bounds() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    bitmap.unset_range(BIT_COUNT..BIT_COUNT);
}

#[test]
fn test_toggle() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    // Bit is initially false
    assert!(!bitmap.is_set(3));

    // First toggle sets it
    let was_set = bitmap.toggle(3);
    assert!(!was_set);
    assert!(bitmap.is_set(3));
    assert_eq!(bitmap.popcount(), 1);

    // Second toggle unsets it
    let was_set = bitmap.toggle(3);
    assert!(was_set);
    assert!(!bitmap.is_set(3));
    assert_eq!(bitmap.popcount(), 0);
}

#[test]
fn test_toggle_twice_equals_original() {
    const BIT_COUNT: usize = 20;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();
    let original = bitmap;

    for idx in 0..BIT_COUNT {
        bitmap.toggle(idx);
    }

    assert_eq!(bitmap, original.bit_not());

    for idx in 0..BIT_COUNT {
        bitmap.toggle(idx);
    }

    assert_eq!(bitmap, original);
}

#[test]
#[should_panic(expected = "Bit index")]
fn test_toggle_out_of_bounds() {
    const BIT_COUNT: usize = 35;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    bitmap.toggle(BIT_COUNT); // should panic
}

#[test]
fn test_bit_or() {
    const BIT_COUNT: usize = 11;
    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, false, false, false, true, true, false,
    ]);
    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, true, false, true, false, false, false, false, false, true, true,
    ]);

    let expected = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, true, true, true, false, false, false, false, true, true, true,
    ]);
    let result = a.bit_or(&b);
    assert_eq!(result, expected);

    let mut c = a;
    c.in_place_bit_or(&b);
    assert_eq!(c, expected);
}

#[test]
fn test_bit_and() {
    const BIT_COUNT: usize = 11;
    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, false, false, false, true, true, false,
    ]);
    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, true, true, true, false, false, false, false, false, true, true,
    ]);

    let expected = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, false, true, false, false, false, false, false, false, true, false,
    ]);
    let result = a.bit_and(&b);
    assert_eq!(result, expected);

    let mut c = a;
    c.in_place_bit_and(&b);
    assert_eq!(c, expected);
}

#[test]
fn test_bit_xor() {
    const BIT_COUNT: usize = 11;
    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, false, false, false, true, true, false,
    ]);
    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, true, true, true, false, false, false, false, false, true, true,
    ]);

    let expected = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, true, false, true, false, false, false, false, true, false, true,
    ]);
    let result = a.bit_xor(&b);
    assert_eq!(result, expected);

    let mut c = a;
    c.in_place_bit_xor(&b);
    assert_eq!(c, expected);
}

#[test]
fn test_bit_not_all_unset() {
    const BIT_COUNT: usize = 20;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    let inverted = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();
    assert_eq!(bitmap.bit_not(), inverted);
}

#[test]
fn test_bit_not_all_set() {
    const BIT_COUNT: usize = 20;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    let inverted = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    assert_eq!(bitmap.bit_not(), inverted);
}

#[test]
fn test_bit_not_inverts_correctly() {
    const BIT_COUNT: usize = 20;
    let original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, true, false, false, false, false, true, false, true, false,
        false, false, true, true, true, false, true,
    ]);

    let inverted = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, true, false, true, false, true, true, true, true, false, true, false, true, true,
        true, false, false, false, true, false,
    ]);

    assert_eq!(original.bit_not(), inverted);
}

#[test]
fn test_in_place_bit_not() {
    const BIT_COUNT: usize = 20;
    let original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, false, false, false, false, true, false, false, true, true, false, true, true,
        false, false, false, true, false, true,
    ]);

    let inverted = original.bit_not();

    let mut inverted_in_place = original;
    inverted_in_place.in_place_bit_not();

    assert_eq!(inverted_in_place, inverted);
}

#[test]
fn test_operator_traits() {
    const BIT_COUNT: usize = 20;
    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, true, false, true, true, false, true, false, true, true,
        false, true, true, false, false, false,
    ]);
    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, true, true, false, true, false, false, true, false, true, true, false, false, true,
        false, false, false, false, false, true,
    ]);

    // bit_and
    assert_eq!(a.bit_and(&b), a & b);
    let mut tmp = a;
    tmp &= b;
    assert_eq!(tmp, a & b);

    // bit_or
    assert_eq!(a.bit_or(&b), a | b);
    let mut tmp = a;
    tmp |= b;
    assert_eq!(tmp, a | b);

    // bit_xor
    assert_eq!(a.bit_xor(&b), a ^ b);
    let mut tmp = a;
    tmp ^= b;
    assert_eq!(tmp, a ^ b);

    // bit_not
    assert_eq!(a.bit_not(), !a);

    // shift_left
    let mut m1 = a;
    m1.shift_left(3);
    assert_eq!(m1, a << 3);
    let mut m2 = a;
    m2 <<= 3;
    assert_eq!(m1, m2);

    // shift_right
    let mut m1 = a;
    m1.shift_right(2);
    assert_eq!(m1, a >> 2);
    let mut m2 = a;
    m2 >>= 2;
    assert_eq!(m1, m2);
}

#[test]
fn test_popcount() {
    const BIT_COUNT: usize = 20;

    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    assert_eq!(a.popcount(), 0);

    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();
    assert_eq!(b.popcount(), BIT_COUNT);

    let c = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, false, false, false, true, false, false, false, true,
        false, false, false, false, false, true, false,
    ]);
    assert_eq!(c.popcount(), 5);
}

#[test]
fn test_first_set_bit() {
    const BIT_COUNT: usize = 20;

    let a = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    assert_eq!(a.first_set_bit(), None);

    let b = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        false, false, false, false, false, true, false, false, true, true, false, false, false,
        false, false, false, false, false, false, false,
    ]);
    assert_eq!(b.first_set_bit(), Some(5));

    let mut c = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[false; 20]);
    c.set(19);
    assert_eq!(c.first_set_bit(), Some(19));
}

#[test]
fn test_shift_left() {
    const BIT_COUNT: usize = 20;
    let mut original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    original.set(0); // set first bit

    let mut bitmap = original;
    bitmap.shift_left(1);
    assert!(bitmap.is_set(1));
    assert_eq!(bitmap.popcount(), 1);
    bitmap.shift_left(7);
    assert!(bitmap.is_set(8)); // moved across a byte boundary
    assert_eq!(bitmap.popcount(), 1);
    bitmap.shift_left(12);
    assert_eq!(bitmap.popcount(), 0); // overflowed and cleared

    let mut bitmap = original;
    bitmap.shift_left(BIT_COUNT);
    assert_eq!(bitmap.popcount(), 0); // overflowed and cleared
}

#[test]
fn test_shift_left_zero_bits() {
    const BIT_COUNT: usize = 20;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set(5);
    bitmap.shift_left(0);
    assert!(bitmap.is_set(5)); // no change
}

#[test]
fn test_shift_left_cleans_unused_bits() {
    const BIT_COUNT: usize = 9; // last 7 bits of the last byte are unused
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    // This will end up in the last byte
    bitmap.set(8);
    bitmap.shift_left(1); // moves bit 8 to bit 9

    // Unused bits must be cleaned / zero
    let raw = bitmap.0[1];
    assert_eq!(raw & !((1 << (BIT_COUNT % 8)) - 1), 0);
}

#[test]
fn test_shift_right() {
    const BIT_COUNT: usize = 20;
    let mut original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    original.set(19); // set last bit

    let mut bitmap = original;
    bitmap.shift_right(1);
    assert!(bitmap.is_set(18));
    assert_eq!(bitmap.popcount(), 1);
    bitmap.shift_right(7);
    assert!(bitmap.is_set(11)); // moved across a byte boundary
    assert_eq!(bitmap.popcount(), 1);
    bitmap.shift_right(12);
    assert_eq!(bitmap.popcount(), 0); // overflowed and cleared

    let mut bitmap = original;
    bitmap.shift_right(BIT_COUNT);
    assert_eq!(bitmap.popcount(), 0); // overflowed and cleared
}

#[test]
fn test_shift_right_zero_bits() {
    const BIT_COUNT: usize = 16;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set(10);
    bitmap.shift_right(0);
    assert!(bitmap.is_set(10)); // no change
}

#[test]
fn test_shift_right_cleans_unused_bits_first() {
    const BIT_COUNT: usize = 9;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();
    bitmap.0[1] |= 1 << 7;
    let raw = bitmap.0[1];
    assert_eq!(raw & !((1 << (BIT_COUNT % 8)) - 1), 128); // 7. bit of unused is set
    bitmap.shift_right(1);

    // Unused bits must be sanitized
    let raw = bitmap.0[1];
    assert_eq!(raw & !((1 << (BIT_COUNT % 8)) - 1), 0); // None of unused are set anymore
    assert_eq!(bitmap.popcount(), 0) // No bits are set
}

#[test]
fn test_rotate_left() {
    const BIT_COUNT: usize = 20;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set(18);
    bitmap.rotate_left(3);

    assert!(bitmap.is_set(1));
    assert!(!bitmap.is_set(18));
    assert_eq!(bitmap.popcount(), 1);

    bitmap.rotate_left(2);
    assert!(bitmap.is_set(3));
    assert!(!bitmap.is_set(1));
    assert_eq!(bitmap.popcount(), 1);
}

#[test]
fn test_rotate_left_skips_unused_bits() {
    const BIT_COUNT: usize = 9;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    assert_eq!(bitmap.popcount(), 9);
    bitmap.rotate_left(7);

    // Unused bits must be skipped / zero
    let raw = bitmap.0[1];
    assert_eq!(raw & !((1 << (BIT_COUNT % 8)) - 1), 0);
    assert_eq!(bitmap.popcount(), 9)
}

#[test]
fn test_rotate_right() {
    const BIT_COUNT: usize = 20;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::new();

    bitmap.set(1);
    bitmap.rotate_right(3);

    assert!(bitmap.is_set(18));
    assert!(!bitmap.is_set(1));
    assert_eq!(bitmap.popcount(), 1);

    bitmap.rotate_right(2);
    assert!(bitmap.is_set(16));
    assert!(!bitmap.is_set(18));
    assert_eq!(bitmap.popcount(), 1)
}

#[test]
fn test_rotate_right_skips_unused_bits() {
    const BIT_COUNT: usize = 9;
    let mut bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::with_all_set();

    assert_eq!(bitmap.popcount(), 9);
    bitmap.rotate_right(7);

    // Unused bits must be skipped / zero
    let raw = bitmap.0[1];
    assert_eq!(raw & !((1 << (BIT_COUNT % 8)) - 1), 0);
    assert_eq!(bitmap.popcount(), 9);
}

#[test]
fn test_rotate_full_cycle() {
    const BIT_COUNT: usize = 20;
    let original = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, true, false, true, false, true, false, false, true, false, true,
        false, true, false, true, false, true,
    ]);

    let mut left_rot = original;
    left_rot.rotate_left(BIT_COUNT);
    assert_eq!(left_rot, original);

    let mut right_rot = original;
    right_rot.rotate_right(BIT_COUNT * 2);
    assert_eq!(right_rot, original);
}

struct Buffer<const N: usize> {
    buf: [u8; N],
    pos: usize,
}

impl<const N: usize> Buffer<N> {
    pub const fn new() -> Self {
        Self {
            buf: [0u8; N],
            pos: 0,
        }
    }

    pub fn as_str(&self) -> &str {
        core::str::from_utf8(&self.buf[..self.pos]).unwrap()
    }
}

impl<const N: usize> Write for Buffer<N> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes = s.as_bytes();
        self.buf[self.pos..self.pos + bytes.len()].copy_from_slice(bytes);
        self.pos += bytes.len();
        Ok(())
    }
}

#[test]
fn debug_format_is_correct() {
    const BIT_COUNT: usize = 9;
    let bitmap = BitMap::<BIT_COUNT, { bucket_count(BIT_COUNT) }>::from_slice(&[
        true, false, true, false, false, false, false, true, false,
    ]);

    let mut buf = Buffer::<128>::new();
    write!(&mut buf, "{:?}", bitmap).unwrap();

    let out = buf.as_str();
    assert_eq!(out, "LSB -> 0: 10100001 8: 0 <- MSB");
}

// SPDX-License-Identifier: LGPL-3.0-or-later

//! Compact byte encoding of polynomials with machine-integer coefficients.

use smallvec::SmallVec;

/// Appends the encoding of a coefficient sequence of length at most 255: its length, then each coefficient as a zigzag varint.
pub(crate) fn pack(words: &[i64], out: &mut Vec<u8>) {
    debug_assert!(words.len() <= u8::MAX as usize);
    out.push(words.len() as u8);
    for &w in words {
        let mut z = ((w << 1) ^ (w >> 63)) as u64;
        while z >= 0x80 {
            out.push(z as u8 | 0x80);
            z >>= 7;
        }
        out.push(z as u8);
    }
}

/// The number of bytes occupied by the encoding that starts the given bytes.
pub(crate) fn packed_len(bytes: &[u8]) -> usize {
    let mut remaining = bytes[0] as usize;
    let mut at = 1;
    while remaining > 0 {
        if bytes[at] < 0x80 {
            remaining -= 1;
        }
        at += 1;
    }
    at
}

/// The coefficient sequence whose encoding starts the given bytes.
pub(crate) fn unpack(bytes: &[u8]) -> SmallVec<[i64; 16]> {
    let count = bytes[0] as usize;
    let mut out = SmallVec::with_capacity(count);
    let mut at = 1;
    for _ in 0..count {
        let mut z = 0u64;
        let mut shift = 0;
        loop {
            let b = bytes[at];
            at += 1;
            z |= ((b & 0x7f) as u64) << shift;
            if b < 0x80 {
                break;
            }
            shift += 7;
        }
        out.push(((z >> 1) as i64) ^ -((z & 1) as i64));
    }
    out
}

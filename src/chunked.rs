// SPDX-License-Identifier: LGPL-3.0-or-later

//! Growable sequence stored in blocks of fixed size.

const BLOCK_BITS: usize = 16;
const BLOCK: usize = 1 << BLOCK_BITS;

/// Sequence that grows a block at a time, without moving the items already stored.
pub(crate) struct Chunked<T> {
    blocks: Vec<Vec<T>>,
    len: usize,
}

impl<T> Default for Chunked<T> {
    fn default() -> Self {
        Chunked {
            blocks: Vec::new(),
            len: 0,
        }
    }
}

impl<T: Copy> Chunked<T> {
    /// The number of items.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Appends an item.
    pub(crate) fn push(&mut self, item: T) {
        if self.len >> BLOCK_BITS == self.blocks.len() {
            self.blocks.push(Vec::with_capacity(BLOCK));
        }
        self.blocks[self.len >> BLOCK_BITS].push(item);
        self.len += 1;
    }

    /// Appends copies of an item until the sequence has at least the given length.
    pub(crate) fn grow(&mut self, len: usize, item: T) {
        while self.len < len {
            if self.len >> BLOCK_BITS == self.blocks.len() {
                self.blocks.push(Vec::with_capacity(BLOCK));
            }
            let block = &mut self.blocks[self.len >> BLOCK_BITS];
            let room = (BLOCK - block.len()).min(len - self.len);
            block.resize(block.len() + room, item);
            self.len += room;
        }
    }

    /// The item at the given position.
    #[inline]
    pub(crate) fn get(&self, at: usize) -> T {
        self.blocks[at >> BLOCK_BITS][at & (BLOCK - 1)]
    }

    /// The item at the given position, if there is one.
    pub(crate) fn find(&self, at: usize) -> Option<T> {
        (at < self.len).then(|| self.get(at))
    }

    /// Mutable access to the item at the given position.
    #[inline]
    pub(crate) fn at(&mut self, at: usize) -> &mut T {
        &mut self.blocks[at >> BLOCK_BITS][at & (BLOCK - 1)]
    }

    /// The items in order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.blocks.iter().flat_map(|b| b.iter().copied())
    }
}

# rectiling

`rectiling` is a Rust library for the exact enumeration of tilings of a rectangle by similar rectangles: tilings in which every tile has the same aspect ratio, in either orientation.
Its main purpose is to compute the number a(n) of distinct tile proportions with which a square can be divided into exactly n similar rectangles ([OEIS A359146](https://oeis.org/A359146)), and the analogous counts for a rectangle of arbitrary rational aspect ratio.
All computations are exact: proportions are identified as real algebraic numbers, by minimal polynomial and root index.

## Setup

The project is a standard Cargo package and has no dependencies outside the Rust ecosystem.

```console
$ cargo build --release
$ cargo test --release
```

## Usage

The command-line tool takes the number of tiles and, optionally, the integer width and height of the main rectangle, which defaults to a square.

```console
$ ./target/release/rectiling 8
$ ./target/release/rectiling --list 5
$ ./target/release/rectiling 7 3 2
```

It prints the number of distinct proportions, their distribution by algebraic degree and counters describing the search; with `--list` it also prints each proportion with its degree, the number of tilings that realise it and its minimal polynomial.
The same search is available from Rust as `rectiling::Search`.

The library reproduces the known values of a(n) for n ≤ 10 and extends the sequence to a(11) = 3446981 and a(12) = 28799493; see [knowledge/results.md](knowledge/results.md).

## Structure

- `src/` — the `rectiling` crate.
- `tests/` — integration tests, exercising the crate through its public interface.
- `benches/` — timings of the search, run with `cargo bench`.
- `knowledge/` — curated notes on the problem, the theory and the algorithms used.

## Licence

Copyright © Stefano Gogioso.
Released under the [GNU Lesser General Public License, version 3 or later](LICENSE); the text of the GNU General Public License, which it supplements, is in [LICENSE.GPL](LICENSE.GPL).

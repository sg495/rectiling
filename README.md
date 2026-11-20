# rectiling

`rectiling` is a Rust library for the exact enumeration of tilings of a rectangle by similar rectangles: tilings in which every tile has the same aspect ratio, in either orientation.
Its main purpose is to compute the number a(n) of distinct tile proportions with which a square can be divided into exactly n similar rectangles ([OEIS A359146](https://oeis.org/A359146)), and the analogous counts for a rectangle of arbitrary rational aspect ratio.
It also counts the tilings themselves, as sets of rectangles: all of them, up to the symmetries of the square, and up to rearrangement of the tiles.
All computations are exact: proportions are identified as real algebraic numbers, by minimal polynomial and root index, and tilings by exact comparison of the coordinates of their tiles.

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
$ ./target/release/rectiling --guillotine 9
$ ./target/release/rectiling --minority 1 9
$ ./target/release/rectiling --tilings 9
$ ./target/release/rectiling --bags 8
$ ./target/release/rectiling --classes 4
$ ./target/release/rectiling --bands 8 11
$ ./target/release/rectiling --band 3 8 11
```

It prints the number of distinct proportions, their distribution by algebraic degree and counters describing the search; with `--list` it also prints each proportion with its degree, the number of tilings that realise it and its minimal polynomial.
With `--guillotine` only guillotine tilings are considered, and with `--minority K` only tilings with at most K tiles in the less frequent orientation.
With `--bands COUNT` the search is run once for each of COUNT bands of proportions and the totals are printed, which divides the memory needed by about COUNT at the cost of more time; with `--band INDEX COUNT` only the band with that index, from 1, is searched, so that the passes can be run separately. COUNT must divide 64.
With `--tilings` it also prints the number of tilings as sets of rectangles, the number of their classes under the symmetries of the main rectangle, computed in two ways, and the numbers of tilings with each kind of symmetry; with `--bags` it adds the number of distinct bags of tiles, and with `--classes` it lists one tiling from each class with the coordinates of its tiles.
With `--exact` every tiling is solved and compared by the reference method, which is slower.
The same searches are available from Rust as `rectiling::Search`.

The library reproduces the known values of a(n) for n ≤ 10 and extends the sequence with a(11) = 3446981, a(12) = 28799493 and a(13) = 250056983; see [knowledge/results.md](knowledge/results.md).
For the tilings themselves it finds 1, 2, 14, 89, 830, 7278, 70410, … tilings and 1, 1, 3, 16, 121, 976, 9051, … classes under symmetry; see [knowledge/tiling-counts.md](knowledge/tiling-counts.md).

## Structure

- `src/` — the `rectiling` crate.
- `tests/` — integration tests, exercising the crate through its public interface.
- `benches/` — timings of the search, run with `cargo bench`.
- `tools/` — an independent reference program in Python that counts tilings by exact coordinates, for cross-checks, and programs that count rooted non-separable planar maps.
- `paper/` — a paper on the method and the results, in Typst, with the programs that draw its figures.
- `knowledge/` — curated notes on the problem, the theory, the algorithms used, the results and their analysis.
- `lean/` — a Lean 4 development proving that both search methods are sound and complete, that proportions persist when tiles are added, and the other propositions of the main body of the paper; see [lean/README.md](lean/README.md).

## Licence

Copyright © Stefano Gogioso.
Released under the [GNU Lesser General Public License, version 3 or later](LICENSE); the text of the GNU General Public License, which it supplements, is in [LICENSE.GPL](LICENSE.GPL).

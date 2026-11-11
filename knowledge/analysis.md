# Analysis of the sequence

This note records what was found when looking for a formula, or for simpler laws, behind a(n) = 1, 1, 3, 11, 51, 245, 1372, 8522, 58347, 433926, 3446981, 28799493, 250056983.
No closed form, recurrence or generating function was found, and the evidence suggests that none of a simple kind exists.
Each statement is labelled *Proved* (the proof is in [structure-proofs.md](structure-proofs.md), which also names anything it assumes), *Argued* (an argument is sketched here and the data agree; nothing is formalised or reviewed), *Conjecture* (agrees with all available data, range stated) or *Heuristic* (loose numerical observation).

## Notation

- S(n): the set of proportions x ≥ 1 for n tiles in a square; a(n) is its size.
- c(x): the least n with x ∈ S(n); ν(n): the number of proportions with c(x) = n.
- g(n): the number of proportions realised by guillotine tilings with n tiles.
- T(n): the number of tilings (placement sequence, orientations, proportion) of the square with bottom-left tile wide.
- m(n, k): the number of proportions realised with n tiles, at most k of them in the less frequent orientation.
- R(x): the aspect ratio of the main rectangle as a function of the proportion, for a fixed arrangement and fixed orientations.
- E(n): the number of distinct R for n tiles up to R ↦ 1/R, over the arrangements and orientations in which no tile vanishes identically in x.
- M(n) = 2·(3n)!/((2n+1)!·(n+1)!), OEIS A000139: the number of rooted non-separable planar maps with n + 1 edges.

## Persistence

*Proved*, also formally in Lean: if n ≥ 2 and k ≥ 3 then S(n) ⊆ S(n + k).

- Three more tiles: cut one tile into four by its mid-lines.
- Five more tiles: cut one tile into six of its own orientation, as a square is cut into six squares.
- Four more tiles, for x > 1: with p = x/(x + 1), place four tiles with sides p and p/x in a pinwheel around the unit square; the central square, of side (x − 1)/(x + 1), holds a reduced copy of the tiling.

The pinwheel degenerates for x = 1, and 1 ∈ S(1) but 1 ∉ S(5); for n ≥ 2 the proportion 1 occurs exactly for n = 4 and n ≥ 6, so the inclusion holds.
Every k ≥ 3 is a sum of threes, fours and fives.
The inclusions hold in the data whenever n + k ≤ 11.
Steps of one and of two fail for most proportions.

| n               | 1   | 2   | 3   | 4   | 5   | 6   | 7    | 8    | 9     | 10     |
| --------------- | --- | --- | --- | --- | --- | --- | ---- | ---- | ----- | ------ |
| a(n)            | 1   | 1   | 3   | 11  | 51  | 245 | 1372 | 8522 | 58347 | 433926 |
| not in S(n + 1) | 1   | 1   | 3   | 11  | 45  | 215 | 1189 | 7371 | 50288 | 374662 |
| not in S(n + 2) | 1   | 1   | 3   | 5   | 38  | 170 | 892  | 5629 | 38957 |        |

Consequently a(n) = ν(n) + β₁(n) + β₂(n) + ν(1) + … + ν(n − 3) for n ≥ 6, where β₁(n) and β₂(n) count the proportions of complexity n − 1 and n − 2 that lie in S(n).
The proportions of S(n) by complexity 1, …, n are as follows.

| n   | a(n)    | proportions by complexity                               |
| --- | ------- | ------------------------------------------------------- |
| 6   | 245     | 1, 1, 3, 5, 5, 230                                      |
| 7   | 1372    | 1, 1, 3, 10, 12, 18, 1327                               |
| 8   | 8522    | 1, 1, 3, 10, 50, 60, 150, 8247                          |
| 9   | 58347   | 1, 1, 3, 10, 50, 230, 435, 949, 56668                   |
| 10  | 433926  | 1, 1, 3, 10, 50, 230, 1327, 2618, 6856, 422830          |
| 11  | 3446981 | 1, 1, 3, 10, 50, 230, 1327, 8247, 17711, 51432, 3367969 |

*Heuristic:* about 12% of the proportions of complexity n − 1 and 31% of those of complexity n − 2 recur at n, and ν(11)/a(11) = 0.977.

## Wide rectangles count the functions

*Proved:* for each n there is W(n) such that for every real w > W(n) the number of proportions for a w × 1 rectangle is E(n); for guillotine tilings it is A338781(n).
The value W(n) = n·(1 + 4ⁿ/2) serves.

1. A tiling with proportion x is an arrangement with orientations for which F(x) = w, where F is R or 1/R, and in which no tile vanishes; the functions F form a finite set closed under inversion.
2. For x ≥ 1 every resistance lies in [1/x, x], so F(1)/x ≤ F(x) ≤ F(1)·x with F(1) ≤ n; hence x ≥ w/n.
3. Each F is odd, so it tends to zero or to infinity at infinity, and inversion exchanges the two kinds; the first kind has no solution for large w, and the second exactly one.
4. Tile sizes are rational in x, so a tile that does not vanish identically does not vanish for large x; it may be negative there, and the tiling then belongs to another arrangement with the same electrical network.
5. Distinct functions agree at finitely many points, so for large w they give distinct proportions.

The count E(n) must leave out the arrangements with orientations in which a tile vanishes identically, such as the pinwheel of five tiles with equal orientations: their functions need not belong to any tiling with n tiles.

The search gives the following counts at w = 1009, 10007, 99991 and 1000003, which agree for n ≤ 9; n = 10 was run at 1009 and 1000003, and n = 11 at 1009 only.

| n           | 1   | 2   | 3   | 4   | 5   | 6   | 7    | 8     | 9      | 10      | 11      |
| ----------- | --- | --- | --- | --- | --- | --- | ---- | ----- | ------ | ------- | ------- |
| all tilings | 1   | 3   | 10  | 38  | 164 | 787 | 4258 | 25767 | 172504 | 1258949 | 9865302 |
| guillotine  | 1   | 3   | 10  | 38  | 161 | 718 | 3385 | 16548 | 83183  | 427490  |         |

The first row agrees with David Einstein's counts of distinct functions for n ≤ 10, obtained by a different method; the value for n = 11 is new and comes from a single run.

*Proved:* in lowest terms R = N/D with one of N and D even, the other odd, and non-negative coefficients, so N − D determines the pair {R, 1/R}.
All roots of N and D are simple and purely imaginary, and the degrees of N and D differ by one.

## Parity of the degree

*Proved:* let R = N/D in lowest terms and d = deg(N − D).
If R tends to 0 at one end of (0, ∞) and to ∞ at the other, then d is odd and R(x) = 1 has an odd number of positive roots, counted with multiplicity; otherwise d and the number of roots are even.
A function of the first kind always has a positive root, and reversing all orientations replaces R(x) by R(1/x), so about half of them have a root ≥ 1; a function of the second kind usually has none.
This accounts for the predominance of odd degrees in the table of [results.md](results.md).

*Heuristic:* the share of proportions of odd degree is 89.4, 87.5, 85.9, 84.6, 83.6, 82.9 and 82.2 per cent for n = 7 to 13.

*Proved:* a proportion realised with k tiles in the less frequent orientation has degree at most 2k + 1, so degree n requires ⌊n/2⌋ such tiles.

## Orientation counts

The table gives m(n, k) for k = 0, 1, 2, …; the last entry of each complete row is a(n).

| n   | m(n, 0), m(n, 1), …                            |
| --- | ---------------------------------------------- |
| 6   | 28, 97, 195, 245                               |
| 7   | 74, 343, 815, 1372                             |
| 8   | 211, 1262, 3586, 6836, 8522                    |
| 9   | 629, 4972, 16560, 35790, 58347                 |
| 10  | 1901, 20432, 80078, 195435, 350688, 433926     |
| 11  | 5772, 87373, 400977, 1099538, 2175986, 3446981 |
| 12  | 17419, 385439, 2062392, 6319032                |
| 13  | 52227, 1743505, 10847852                       |
| 14  | 155656, 8022248                                |

The column k = 0 counts the rectangles that can be dissected into n squares: it reproduces the eight published terms of OEIS A210517 and continues 629, 1901, 5772, 17419, 52227, 155656 for n = 9 to 14.
These six terms were computed here only.

## Rational proportions

| n   | rational | one orientation | only with both orientations |
| --- | -------- | --------------- | --------------------------- |
| 6   | 30       | 28              | 5/3, 2                      |
| 7   | 76       | 74              | 3/2, 3                      |
| 8   | 214      | 211             | 5/3, 5/2, 4                 |
| 9   | 633      | 629             | 8/3, 16/5, 7/2, 5           |
| 10  | 1904     | 1901            | 11/3, 9/2, 6                |
| 11  | 5775     | 5772            | 14/3, 11/2, 7               |
| 12  | 17422    | 17419           | 17/3, 13/2, 8               |
| 13  | 52230    | 52227           | 20/3, 15/2, 9               |

*Conjecture:* for every n ≥ 10 the rational proportions of S(n) that cannot be realised with one orientation are exactly n − 4, n − 11/2 and n − 19/3.

- It was stated from n = 10 and 11 and then confirmed for n = 12 and 13.
- *Proved:* the three proportions are the three largest for which n − 4 tiles of one orientation suffice, and they lie in S(n) by the pinwheel.
- *Proved:* the rectangles of sides n − 4 and n − 11/2 by 1 cannot be cut into n squares; for n − 19/3 the same is proved from the fact, known by computation only, that the 5 × 3 rectangle cannot be cut into eight squares.
- What remains conjectural is that there is no other exception.
- The exceptions 5/3 for n = 6 and 16/5 for n = 9 come from pinwheels whose central rectangle is not a square.

The number of rational proportions would then be A210517(n) + 3 for n ≥ 10.

## Guillotine tilings

| n   | a(n)     | g(n)    | a(n) − g(n) | g(n)/a(n) | A338781(n) |
| --- | -------- | ------- | ----------- | --------- | ---------- |
| 5   | 51       | 51      | 0           | 1         | 161        |
| 6   | 245      | 221     | 24          | 0.902     | 718        |
| 7   | 1372     | 1069    | 303         | 0.779     | 3385       |
| 8   | 8522     | 5275    | 3247        | 0.619     | 16548      |
| 9   | 58347    | 26765   | 31582       | 0.459     | 83183      |
| 10  | 433926   | 138521  | 295405      | 0.319     | 427490     |
| 11  | 3446981  | 728723  | 2718258     | 0.211     | 2237196    |
| 12  | 28799493 | 3877342 | 24922151    | 0.135     | 11865560   |

The values g(11) and g(12) were computed once.

*Proved:* g(n) ≤ n·A338781(n), and A338781(n) is at most half the number of series–parallel networks on n edges of two kinds.
That number grows as 6.1589ⁿ·n^(−3/2), where the constant is numerical and the form of the asymptotics is the standard one, not proved; so the growth constant of g(n) is at most 6.159.

*Conjecture:* g(n)/a(n) → 0.

## Growth

*Proved:* a(n) ≤ n·2ⁿ⁻¹·M(n), given Tutte's enumeration of rooted non-separable planar maps, so the growth constant of a(n) is at most 27/2.
The network of a tiling, with an additional edge joining its poles, is such a map with n + 1 edges.

*Argued:* 2ⁿ⁻² ≤ g(n) ≤ a(n) ≤ T(n) ≤ n·2ⁿ⁻¹·M(n).
The last inequality needs in addition that a mosaic class is determined by its map and the directions of its edges, and that each class has one placement sequence; neither is proved here.

*Conjecture:* T(n)/(2ⁿ⁻¹·M(n)) converges to a constant near 0.30: the values are 0.3001, 0.2996, 0.3003, 0.3004, 0.3011, 0.3016 and 0.3022 for n = 7 to 13.
The ratio creeps upward, so the safer statement is that T(n)^(1/n) → 27/2.

*Conjecture:* a(n + 1)/a(n) is non-decreasing: 1, 3, 3.67, 4.64, 4.80, 5.60, 6.21, 6.85, 7.44, 7.94, 8.36, 8.68.
The same statement is false for g(n).

*Heuristic:* the growth constant of a(n) lies between 11 and 13.5.
Two-point fits of a(n)/a(n − 1) = μ(1 + α/n) give μ between 12.6 and 13.0 with α about −4, but the same fit on the Baxter numbers is about 5% low, and three-point fits are unstable.

*Heuristic:* a(n)/E(n) = 0.311, 0.322, 0.331, 0.338, 0.345, 0.349 for n = 6 to 11.

## The main rectangle as a parameter

The number of proportions for a w × 1 rectangle, for w = 1, 2, 3, …:

| n   | counts                                                                                                                           |
| --- | -------------------------------------------------------------------------------------------------------------------------------- |
| 5   | 51, 127, 154, 158, 161, 164, 162, 164, then 164                                                                                  |
| 6   | 245, 645, 727, 777, 783, 780, 787, 787, 785, 786, then 787                                                                       |
| 7   | 1372, 3544, 4049, 4200, 4235, 4251, 4251, 4253, 4258, 4258, 4256, 4258, 4256, then 4258                                          |
| 8   | 8522, 22046, 24758, 25513, 25666, 25747, 25750, 25756, 25765, 25764, 25761, 25767, 25764, 25767, 25767, 25765, 25766, then 25767 |

*Conjecture:* for integer w ≥ ⌊n²/4⌋ + 2 the count is E(n), and for w = ⌊n²/4⌋ + 1 it is E(n) − 1 for even n and E(n) − 2 for odd n.

- Mechanism, *proved*: a wide tiles in a row beside a block of b tiles, either tall side by side or wide and stacked, give the functions a·x + b/x and a·x + x/b, which share the root x = b at w = ab + 1, with a + b = n.
- Evidence: n = 2 to 8 for w ≤ 30; predicted and then confirmed for n = 9, with 172502 at w = 21 and 172504 at w = 22, 23, 24, 25 and 30.
- Unproved: that no other pair of functions shares a root beyond that width, and that at that width nothing else changes the count; the width proved sufficient, n·(1 + 4ⁿ/2), is exponential.

*Conjecture (weak):* the count never exceeds E(n), for any rational w; it holds for n ≤ 8 on 30 integers and 16 fractions, and no argument is known.

The count is not monotone in w: it dips at the widths w = ab + 1.

## What does not work

- No linear recurrence with constant coefficients of order at most 5 for a(n), g(n) or the rational column.
- No recurrence with polynomial coefficients of (order, degree) (1,1), (1,2), (1,3), (1,4), (2,1), (2,2) or (3,1); the same test recovers the recurrence of the Baxter numbers at (2,2), and larger shapes cannot be tested with thirteen terms.
- Differences, the binomial transform and its inverse, and the inverse Euler and inverse INVERT transforms give no match in the OEIS.
- No OEIS match for g(n), a(n) − g(n), ν(n), the rational column, the new terms of A210517, E(n) or T(n).
- The residues of a(n) modulo 2 to 13 show no pattern.
- The quotients a(n)/T(n), a(n)/(2ⁿ⁻¹·B(n)), a(n)/E(n) and g(n)/A338781(n) are not constant.
- S(n) ⊆ S(n + 1) and S(n) ⊆ S(n + 2) fail.
- The number of distinct polynomials reported by the search is not an invariant of the problem: it depends on the version of the engine.

## Routes to proofs

The proofs obtained since are in [structure-proofs.md](structure-proofs.md); what remains is the following.

- A width W(n) of polynomial size, and the exact threshold ⌊n²/4⌋ + 2.
- For the rational proportions, a proof by hand that the 5 × 3 rectangle cannot be cut into eight squares, and exhaustiveness, which looks harder.
- For the growth of T(n), the two combinatorial facts named above; a lower bound needs a family of tilings in which no tile vanishes at the root.
- The growth constant of a(n) and the convergence of T(n)/(2ⁿ⁻¹·M(n)) look out of reach.

## Reproducing

```console
$ cargo build --release
$ ./target/release/rectiling --guillotine 11
$ ./target/release/rectiling --minority 2 11
$ ./target/release/rectiling 10 1009 1
$ ./target/release/rectiling --guillotine 10 1000003 1
$ ./target/release/rectiling --list --minority 0 12
$ cargo run --release --example inclusions 9
```

The run `--guillotine 12` takes 80 seconds and 43 GB of memory.
The inclusion tables for n = 10 and 11, the fits and the recurrence tests were made with scripts that are not in the repository.

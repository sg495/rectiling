# Results

All values on this page were computed with the default method of the `rectiling` crate on 11 November 2026, on a 16-core Apple M4 Max with 128 GB of memory.
Every run reported no singular system, no case with aspect ratio independent of the proportion, and no arithmetic overflow, so every value is certified in the sense of [solving.md](solving.md).

## The square

| n  | a(n)     | status                                              |
| -- | -------- | --------------------------------------------------- |
| 1  | 1        | agrees with the OEIS                                |
| 2  | 1        | agrees with the OEIS                                |
| 3  | 3        | agrees with the OEIS                                |
| 4  | 11       | agrees with the OEIS                                |
| 5  | 51       | agrees with the OEIS                                |
| 6  | 245      | agrees with the OEIS                                |
| 7  | 1372     | agrees with the OEIS                                |
| 8  | 8522     | agrees with Henderson and Einstein                  |
| 9  | 58347    | agrees with Einstein; first independent confirmation |
| 10 | 433926   | agrees with Einstein; first independent confirmation |
| 11 | 3446981  | new                                                 |
| 12 | 28799493 | new                                                 |

The values for n = 11 and n = 12 come from this computation alone and have not been confirmed by a second method.

### Work performed

A *case* is a placement sequence together with an orientation vector, with the bottom-left tile wide; a *tiling* is a case together with a proportion that it realises.

| n  | cases       | cases with a candidate root | tilings    | distinct polynomials | seconds |
| -- | ----------- | --------------------------- | ---------- | -------------------- | ------- |
| 5  | 1472        | 453                         | 421        | 73                   | 0.01    |
| 6  | 13504       | 4217                        | 3981       | 351                  | 0.01    |
| 7  | 132736      | 41159                       | 37219      | 1978                 | 0.03    |
| 8  | 1376512     | 427063                      | 368663     | 12171                | 0.13    |
| 9  | 14899712    | 4623709                     | 3793179    | 81190                | 1.0     |
| 10 | 167034880   | 51902438                    | 40013433   | 584399               | 10.3    |
| 11 | 1928151040  | 600220519                   | 432396494  | 4476286              | 116     |
| 12 | 22815866880 | 7116079030                  | 4758270004 | 36174631             | 1353    |

The run for n = 12 used 21.6 GB of memory.
About 0.8% of the cases are passed to the reference method, almost always because a tile degenerates to a segment at the candidate root.

### Algebraic degrees

The number of proportions of each algebraic degree.

| n  | 1     | 2    | 3      | 4      | 5       | 6       | 7        | 8       | 9       | 10     | 11     | 12    |
| -- | ----- | ---- | ------ | ------ | ------- | ------- | -------- | ------- | ------- | ------ | ------ | ----- |
| 1  | 1     |      |        |        |         |         |          |         |         |        |        |       |
| 2  | 1     | 0    |        |        |         |         |          |         |         |        |        |       |
| 3  | 2     | 0    | 1      |        |         |         |          |         |         |        |        |       |
| 4  | 5     | 0    | 6      | 0      |         |         |          |         |         |        |        |       |
| 5  | 11    | 2    | 32     | 2      | 4       |         |          |         |         |        |        |       |
| 6  | 30    | 7    | 136    | 11     | 59      | 2       |          |         |         |        |        |       |
| 7  | 76    | 16   | 560    | 92     | 546     | 38      | 44       |         |         |        |        |       |
| 8  | 214   | 53   | 2254   | 475    | 3922    | 500     | 1065     | 39      |         |        |        |       |
| 9  | 633   | 156  | 9250   | 2327   | 24970   | 4493    | 14414    | 1244    | 860     |        |        |       |
| 10 | 1904  | 476  | 38540  | 10695  | 149454  | 33780   | 149433   | 20498   | 27943   | 1203   |        |        |
| 11 | 5775  | 1392 | 164780 | 47420  | 861112  | 226177  | 1320602  | 243220  | 508761  | 45842  | 21900  |       |
| 12 | 17422 | 4333 | 721574 | 208870 | 4849698 | 1396981 | 10497127 | 2360993 | 6867895 | 928974 | 906538 | 39088 |

The first column counts the rational proportions.
A rational proportion arises whenever all tiles have the same orientation, the main square then being cut into smaller squares after a change of scale along one axis.
The number of rectangles that can be dissected into n squares ([OEIS A210517](https://oeis.org/A210517): 1, 1, 2, 5, 11, 28, 74, 211) agrees with the column up to n = 5 and is exceeded by it from n = 6 onwards (30, 76 and 214 against 28, 74 and 211).
This suggests that some rational proportions are obtained with n tiles only by using both orientations; the comparison has not been examined case by case.

## Other main rectangles

The number of proportions for a main rectangle of aspect ratio w.
Each count was obtained for both w and 1/w where indicated, with identical lists of proportions.

| n | w = 2 | w = 3 | w = 3/2 | w = 4/3 | w = 5/2 |
| - | ----- | ----- | ------- | ------- | ------- |
| 1 | 1     | 1     | 1       | 1       | 1       |
| 2 | 2     | 3     | 2       | 2       | 3       |
| 3 | 8     | 8     | 5       | 6       | 8       |
| 4 | 29    | 35    | 26      | 22      | 30      |
| 5 | 127   | 154   | 119     | 111     | 143     |
| 6 | 645   | 727   | 542     | 539     | 711     |
| 7 | 3544  | 4049  | 3125    | 3012    | 3893    |
| 8 | 22046 | 24758 | 19356   | 18712   | 23928   |
| 9 | 150362 | 167263 | 132682 | 127163  | 161991  |

The counts for w = 1/2, 1/3 and 2/3 were computed separately for n = 6, 7 and 8 and agree with those for w = 2, 3 and 3/2.

## Reproducing

```console
$ cargo build --release
$ ./target/release/rectiling 12
$ ./target/release/rectiling --list 7
$ ./target/release/rectiling 9 3 2
```

The first command line computes a(12), the second lists the 1372 proportions for seven tiles with their minimal polynomials, and the third treats a main rectangle of aspect ratio 3/2 with nine tiles.

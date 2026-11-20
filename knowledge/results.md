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
| 13 | 250056983 | new                                                |

The values for n = 11, 12 and 13 come from this computation alone and have not been confirmed by a second method.
The values for n = 11 and n = 12 were each obtained twice, before and after a substantial reworking of the search, with identical counts of tilings and identical degree distributions; the value for n = 13 was also obtained twice, before the tables were made more compact and with version 1.0.0, with identical counts of cases, tilings and polynomials and identical degree distributions.

### Work performed

A *case* is a placement sequence together with an orientation vector, with the bottom-left tile wide; a *tiling* is a case together with a proportion that it realises.

| n  | cases        | cases with a candidate root | tilings     | distinct polynomials | seconds |
| -- | ------------ | --------------------------- | ----------- | -------------------- | ------- |
| 5  | 1472         | 453                         | 421         | 63                   | 0.01    |
| 6  | 13504        | 4217                        | 3981        | 310                  | 0.01    |
| 7  | 132736       | 41159                       | 37219       | 1660                 | 0.02    |
| 8  | 1376512      | 427063                      | 368663      | 10123                | 0.10    |
| 9  | 14899712     | 4623709                     | 3793179     | 67035                | 0.66    |
| 10 | 167034880    | 51902438                    | 40013433    | 485269               | 6.6     |
| 11 | 1928151040   | 600220519                   | 432396494   | 3774031              | 75      |
| 12 | 22815866880  | 7116079030                  | 4758270004  | 30989074             | 888     |
| 13 | 275783647232 | 86194353821                 | 53198408925 | 264866132            | 11175   |

The number of cases is 2ⁿ⁻¹ times the Baxter number.
The run for n = 12 used 6.5 GB of memory and that for n = 13 about 41 GB.
These timings and memory figures are those of the runs that produced the values; the tables were made more compact afterwards, see below.
About one case in ten thousand is passed to the reference method.
The search spends about 0.6 microseconds of processor time per case; a term further would take some twelve times longer than n = 13 and was not attempted.

### Memory and bands

The shared tables were later made more compact and the search was given the option of running in bands of proportions (see [solving.md](solving.md)).
The values, the degree distributions and the counters are unchanged; the figures below are for the same machine, with peak resident memory.

| n  | run          | seconds, before | seconds, after | memory, before | memory, after |
| -- | ------------ | --------------- | -------------- | -------------- | ------------- |
| 10 | single       | 6.7             | 7.0            | 0.26 GB        | 0.15 GB       |
| 11 | single       | 78              | 78             | 1.86 GB        | 1.07 GB       |
| 11 | with tilings | 128             | 125            | 1.8 GB         | 1.06 GB       |
| 11 | 8 bands      |                 | 319            |                | 0.28 GB       |
| 12 | single       | 888             | 915            | 6.5 GB         | 4.4 GB        |
| 12 | 8 bands      |                 | 4037           |                | 1.2 GB        |
| 13 | single       | 11175           | 12140          | 41 GB          | 30.3 GB       |

- A single search takes the same time as before, or some 9% more for n = 13, and between two thirds and three quarters of the memory; between n = 11 and n = 12 the memory grows by some 120 bytes for each further proportion equation, against 170 before.
- A pass over one of K bands takes a fraction of about 1/2 + 1/(2K) of the time of a single search, so eight bands take 4.4 times as long, with a peak memory smaller by a factor of 3.7 for n = 12. The factor is below eight because a few hundred megabytes belong to the threads and not to the tables.
- The eight passes for n = 12 give 28799493 proportions, the same degree distribution and the same 4758270004 tilings as the single search, which is a further check of a(12), though not an independent one.

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

For n = 13 the counts by degree, from 1 to 13, are 52230, 13531, 3226298, 912764, 27008697, 8173821, 77488650, 19961337, 76665843, 13546609, 20575413, 1782742 and 649048.

The first column counts the rational proportions.

### Rational proportions

When all tiles have the same orientation, stretching one axis by the proportion turns the tiling into a dissection of a rectangle into n squares, and the proportion is the aspect ratio of that rectangle.
The proportions obtained in this way are counted by [OEIS A210517](https://oeis.org/A210517), the number of rectangles that can be dissected into n squares: 1, 1, 2, 5, 11, 28, 74, 211.

The first column of the table agrees with that sequence up to n = 5 and exceeds it afterwards, and the excess consists of rational proportions that can be realised with n tiles only by using both orientations.
They were identified by searching, for each rational proportion p/q found with n tiles, for a dissection of the p × q rectangle into n squares.

| n | rational proportions | with one orientation | only with both orientations |
| - | -------------------- | -------------------- | --------------------------- |
| 4 | 5                    | 5                    | none                        |
| 5 | 11                   | 11                   | none                        |
| 6 | 30                   | 28                   | 5/3, 2                      |
| 7 | 76                   | 74                   | 3/2, 3                      |
| 8 | 214                  | 211                  | 5/3, 5/2, 4                 |

For example, a 2 × 1 rectangle cannot be cut into exactly six squares, but a square can be cut into six rectangles of proportion 2 if some are wide and some are tall.
The middle column reproduces the published sequence, which is a further check on the search.
A proportion listed for one n may well be realised with a single orientation for another n: 2 is, for two tiles.

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
$ ./target/release/rectiling 13
$ ./target/release/rectiling --list 7
$ ./target/release/rectiling 9 3 2
```

The first command line computes a(13), which takes about three and a half hours and 30 GB of memory on the machine above, the second lists the 1372 proportions for seven tiles with their minimal polynomials, and the third treats a main rectangle of aspect ratio 3/2 with nine tiles.

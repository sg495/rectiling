// SPDX-License-Identifier: LGPL-3.0-or-later
#import "template.typ": template, appendix, proposition, conjecture, definition, example, proof
#import "tables.typ": datatable

#let todo(body) = text(fill: rgb("#b00020"))[[To do: #body]]

#show: template.with(
  title: [Enumerating the Dissections of a Square into Similar Rectangles],
  authors: ((name: "Stefano Gogioso", affil: "Hashberg"),),
  abstract: [#todo[abstract, to be written once the headline results are settled.]],
  keywords: [tilings, similar rectangles, rectangulations, Baxter numbers, exact enumeration, real algebraic numbers],
)

= Introduction <sec:intro>

A rectangle can be cut into finitely many rectangles that are all similar to one another, each lying either way round, and one may ask which proportions the pieces can have.
For a square cut into two pieces the only possibility is a pair of halves, of proportion $2$.
For three pieces there are three: thirds, of proportion $3$; a half-height slab on two quarter-size pieces, of proportion $3 slash 2$; and a third arrangement, in which no two pieces are congruent, whose proportion $1.7548...$ is the real root of $x^3 - 2 x^2 + x - 1$, the square of the plastic ratio.

The qualitative question was settled in the 1990s.
Dehn had shown that a rectangle can be cut into squares only if its sides are commensurable @dehn1903, and Brooks, Smith, Stone and Tutte had recast dissections of rectangles as planar electrical networks @bsst1940.
Freiling and Rinne @freiling1994, and independently Laczkovich and Szekeres @laczkovich1995, proved that a square can be cut into rectangles of proportion $x$, for some number of pieces, exactly when $x$ is algebraic and all its conjugates have positive real part; the case of a rectangle cut into rectangles was treated by Freiling, Laczkovich and Rinne @flr1997, and the electrical point of view was developed further by Prasolov and Skopenkov @prasolov2011.

The quantitative question is recent.
In December 2022 Baez asked how many proportions are possible when the number $n$ of pieces is fixed @baez2022, and a collaborative effort followed, reported in @baez2022 @baez2023 and in the press @roberts2023.
The resulting sequence $a(n)$ is entry A359146 of the OEIS @oeisA359146, which lists $1, 1, 3, 11, 51, 245, 1372$ for $n <= 7$.
The values for $n <= 7$ were obtained by exhaustive searches of Henderson @henderson2023 and of Gerbet, reported in @baez2023; Henderson also found $a(8) = 8522$.
Taams proved that the proportion is algebraic of degree at most $n$ @taams2023.
Einstein, using the correspondence with electrical networks, reported $a(9) = 58347$ and $a(10) = 433926$ @einstein2023; these two values have not, to our knowledge, been published elsewhere or reproduced.
No formula, recurrence or asymptotic estimate for $a(n)$ is known.

This paper describes an exact search procedure for the problem, for a main rectangle of arbitrary rational aspect ratio, and the results obtained with it.
The procedure builds tilings one tile at a time over a staircase-shaped frontier, turns each combinatorial arrangement into a linear system whose coefficients are polynomials in the proportion, and solves that system exactly, so that every proportion is identified as a real algebraic number by its minimal polynomial.
We reproduce all the values above, by a method independent of both earlier ones, and extend the sequence by three terms:
$ a(11) = 3446981, quad a(12) = 28799493, quad a(13) = 250056983. $

@sec:tilings fixes definitions.
@sec:search presents the search procedure and proves it sound and complete.
@sec:optimisations presents the optimisations that make thirteen tiles feasible, with the propositions that justify them.
@sec:results reports the results.
#todo[state here whether the correctness propositions have been formalised in Lean, once that work is complete.]

= Tilings <sec:tilings>

We work in the plane with axis-parallel rectangles.
A rectangle is determined by its bottom-left corner and its two side lengths, and its proportion disregards which side is the longer.

#definition(name: [rectangle])[
  A _rectangle_ is a set $R = [a, a + w] times [b, b + h]$ with $w, h > 0$; its _width_ is $w$, its _height_ is $h$ and its _anchor_ is the point $(a, b)$.
  The _aspect ratio_ of $R$ is $w slash h$ and its _proportion_ is $max(w slash h, h slash w) >= 1$.
  The rectangle is _wide_ if $w >= h$ and _tall_ if $h >= w$.
] <def:rectangle>

A tiling is a dissection in the usual sense: the tiles cover the main rectangle and overlap only along their boundaries.

#definition(name: [tiling])[
  A _tiling_ of a rectangle $M$ is a finite set of rectangles, its _tiles_, whose union is $M$ and whose interiors are pairwise disjoint.
  A tiling is _similar of proportion $x$_ if every tile has proportion $x$.
] <def:tiling>

Scaling the plane preserves proportions, so only the aspect ratio of the main rectangle matters, and we normalise its height to one.

#definition(name: [achievable proportions])[
  For a real number $w > 0$ and an integer $n >= 1$, let $P_n (w)$ be the set of those $x >= 1$ for which the rectangle $[0, w] times [0, 1]$ has a similar tiling of proportion $x$ with exactly $n$ tiles.
  We write $a_w (n) := |P_n (w)|$ and $a(n) := a_1 (n)$.
] <def:counts>

The sets $P_n (w)$ are finite: this follows from @prop:complete, which exhibits each proportion as a root of one of finitely many non-zero polynomials.

Two elementary observations are used throughout.
The first is that exchanging the two axes turns a tiling of a rectangle of aspect ratio $w$ into one of aspect ratio $1 slash w$, turning wide tiles into tall ones.

#proposition(name: [transposition])[
  For all $w > 0$ and $n >= 1$, $P_n (w) = P_n (1 slash w)$.
] <prop:transposition>

#proof[
  The map $(u, v) |-> (v slash w, u slash w)$ sends $[0, w] times [0, 1]$ onto $[0, 1 slash w] times [0, 1]$ and sends rectangles to rectangles of the same proportion.
]

The second is that the sets of proportions grow with $n$ along steps of three.
Whether they grow along steps of one is not known to us.

#proposition(name: [subdivision])[
  For all $w > 0$ and $n >= 1$, $P_n (w) subset.eq P_(n + 3) (w)$.
] <prop:subdivision>

#proof[
  Cutting one tile of a similar tiling into four congruent quarters, by the two lines through its centre, gives a similar tiling of the same proportion with three more tiles.
]

@fig:three shows every similar tiling of the unit square with three tiles whose bottom-left tile is wide, as found by the procedure of @sec:search; the remaining ones are their transposes.

#figure(
  image("figures/three-tiles.svg", width: 100%),
  caption: [The similar tilings of a square with three tiles in which the bottom-left tile is wide, labelled by proportion. Tiles are coloured in the order in which the search places them.],
) <fig:three>

= Search procedure <sec:search>

== Staircases <sec:staircase>

The search places tiles one at a time, starting at the bottom-left corner of the main rectangle, in such a way that the region already covered is always closed under moving left and down.
The boundary between the covered and the uncovered region is then a staircase descending from left to right, and the next tile always sits in one of its concave corners.

#definition(name: [staircase])[
  Let $M = [0, W] times [0, H]$.
  A _staircase_ in $M$ is a sequence of points $(a_0, b_0), dots, (a_(k - 1), b_(k - 1))$ of $M$, with $k >= 0$, such that $0 <= a_0 < dots < a_(k - 1) < W$ and $H > b_0 > dots > b_(k - 1) >= 0$, where moreover $a_0 = 0$ and $b_(k - 1) = 0$ if $k >= 1$.
  Its $i$-th _tier_ is the rectangle $T_i = [a_i, W] times [b_i, b_(i - 1)]$, with $b_(-1) := H$; the point $(a_i, b_i)$ is the _anchor_ of the tier, $L_i := a_(i + 1) - a_i$ is its _floor_, with $a_k := W$, and $M_i := b_(i - 1) - b_i$ is its _wall_.
  The _uncovered region_ of the staircase is the union of its tiers.
] <def:staircase>

The staircase with the single anchor $(0, 0)$ has $M$ itself as its only tier, and the empty staircase has empty uncovered region.
@fig:staircase shows a staircase with four tiers.

#figure(
  image("figures/staircase.svg", width: 38%),
  caption: [A partial tiling and its staircase. Anchors are circled, tiers are outlined, and the hatched part of each tier is the region within which a tile placed at its anchor must fit.],
) <fig:staircase>

A tile placed at the anchor of a tier may or may not be as wide as the floor, and may or may not be as high as the wall.
This gives four kinds of placement, each of which turns a staircase into another.

#definition(name: [placement])[
  Let $T_i$ be a tier of a staircase, with floor $L$ and wall $M$.
  A rectangle $R$ of width $w$ and height $h$ with the same anchor as $T_i$ _fits_ the tier if $w <= L$ and $h <= M$.
  Its _fit_ is _inside_ if $w < L$ and $h < M$, _full height_ if $w < L$ and $h = M$, _full width_ if $w = L$ and $h < M$, and _full_ if $w = L$ and $h = M$.
  _Placing_ $R$ replaces the staircase by the one whose uncovered region is the closure of the old uncovered region minus $R$.
] <def:placement>

Concretely, an inside placement replaces the anchor by two, one above the tile and one to its right; a full-height placement moves the anchor to the right and lengthens the floor of the previous tier by $w$; a full-width placement moves the anchor up and heightens the wall of the next tier by $h$; and a full placement removes the anchor, lengthening the floor of the previous tier by $L$ and heightening the wall of the next by $M$.
The number of tiers thus increases by one, stays the same, or decreases by one.

Every tiling can be built by placements.
The proof singles out, at each stage, the first tier whose tile fits, and this choice will also serve to make the construction canonical.

#proposition(name: [staircase construction])[
  Let $cal(T)$ be a tiling of $M$ and let $S$ be a staircase whose uncovered region is a union of tiles of $cal(T)$ and is not empty.
  Then the tile of $cal(T)$ anchored at the anchor of some tier of $S$ fits that tier.
  Consequently the tiles of $cal(T)$ can be ordered as $R_1, dots, R_n$ so that $R_j$ is placed, in the sense of @def:placement, on the staircase left by $R_1, dots, R_(j - 1)$, starting from the staircase of $M$ and ending with the empty one.
] <prop:construction>

#proof[
  For each tier $T_i$, the point just above and to the right of its anchor is uncovered, and the tile $R^((i))$ of $cal(T)$ containing it must have that anchor, since the points to the left of the anchor and below it are covered or outside $M$.
  The tile $R^((0))$ is no higher than the wall of $T_0$, which reaches the top of $M$.
  If $R^((i))$ is no higher than the wall of $T_i$ but wider than its floor, then it covers points directly above the floor of $T_(i + 1)$ at the height of the anchor of $T_i$, so $R^((i + 1))$, which cannot overlap it, is no higher than the wall of $T_(i + 1)$.
  The tile at the last tier cannot be wider than its floor, which reaches the right side of $M$.
  Hence the least $i$ for which $R^((i))$ is no wider than the floor of $T_i$ exists, and for it $R^((i))$ fits.
  Placing that tile gives a staircase whose uncovered region is again a union of tiles, and induction on the number of uncovered tiles gives the ordering.
]

== Canonical sequences <sec:canonical>

A tiling generally admits several orderings as in @prop:construction, and the search must visit each tiling once.
We fix the ordering by always placing the tile at the first tier at which the tile fits, as in the proof above.

#definition(name: [canonical sequence])[
  A tier of a staircase arising in the construction of a tiling $cal(T)$ is _ready_ if the tile of $cal(T)$ at its anchor fits it.
  The _canonical sequence_ of $cal(T)$ is the sequence of placements obtained by placing, at each stage, the tile at the ready tier of least index.
  Each placement is recorded as a triple of the index of the tier, the fit, and the orientation of the tile, wide or tall.
] <def:canonical>

A square tile is both wide and tall, so that a tiling by squares has several records; this multiplicity is harmless, since only proportions are counted.

The search enumerates candidate records without knowing the tiling, so it needs a description of the records that can be canonical.
When a tile is placed at tier $i$, the canonical rule asserts that no tier of smaller index was ready.
Such a tier can become ready only if its floor grows, which happens when a tile of full height is placed at the next tier.

#definition(name: [stale tier])[
  In a sequence of placements, a tier becomes _stale_ when a tile is placed at a tier of larger index, and ceases to be stale when its floor is lengthened or when a tile is placed at it.
  A sequence of placements is _admissible_ if no tile is placed at a stale tier.
] <def:stale>

#proposition[
  The canonical sequence of every tiling is admissible.
] <prop:stale>

#proof[
  Suppose that tier $j$ became stale when a tile was placed at tier $i > j$, and that its floor and its anchor have not changed since.
  The wall of tier $j$ can have changed only through a full-width or full placement at tier $j - 1$, which requires tier $j - 1$ to have become ready after becoming stale; by induction on $j$ this requires a change of the floor of some tier of index at most $j$ after a placement at a larger index, hence a full-height or full placement at tier $j$ or below, which moves or removes the anchor of tier $j$ or lengthens its floor.
  So the tier is exactly as it was when the canonical rule passed over it, and its tile is still not ready.
]

#todo[the converse refinement used by the implementation, that a tile placed on a tier whose floor has grown since it became stale must be wider than the floor as it was, is not needed once tilings are grouped as in @sec:mosaic; decide whether to state it.]

== The linear system <sec:system>

Fix a complete admissible record: a sequence of $n$ triples that leads from the staircase of $M$ to the empty staircase.
The sizes of the tiles are constrained by the record, and the constraints are linear once the proportion is fixed.

Let the main rectangle have height $1$ and width $W$, and let $x >= 1$ be the proportion.
A wide tile with short side $s$ has width $x s$ and height $s$; a tall one has width $s$ and height $x s$.
The short side of a tile placed inside its tier is a free unknown.
A full-height tile has the height of the wall, so its width is that height multiplied by $x$ if it is wide and divided by $x$ if it is tall; a full-width tile is treated symmetrically.
A full tile has the width of the floor and the height of the wall, which must therefore be in the ratio prescribed by its orientation.

#definition(name: [system of a record])[
  Let $rho$ be a complete admissible record with $k$ inside placements.
  Its _unknowns_ are $W$ and the short sides $s_1, dots, s_k$ of the tiles placed inside.
  Every floor and wall arising along $rho$ is a linear form in $1, W, s_1, dots, s_k$ with coefficients in $ZZ[x, x^(-1)]$.
  The _system_ of $rho$ consists of one equation for each full placement, $L = x M$ for a wide tile and $M = x L$ for a tall one, where $L$ and $M$ are the floor and wall of its tier, together with one strict inequality for each placement, stating that the short side of the tile is positive.
] <def:system>

The number of tiers increases by one with each inside placement and decreases by one with each full placement, from one to zero, so a complete record has $k + 1$ full placements and its system has $k + 1$ equations in $k + 1$ unknowns.

#example[
  Consider the record that places a wide tile of full width, then a tall tile of full height, then a wide full tile, all at tier $0$.
  The first tile has width $W$ and height $W slash x$, leaving a tier of floor $W$ and wall $1 - W slash x$.
  The second has that wall as its height $h$ and width $h slash x$, and the third has width $W - h slash x$ and height $h$, so the system is the single equation $W - h slash x = x h$ with $h = 1 - W slash x$, that is,
  $ W = (x^3 + x) / (2 x^2 + 1), $
  with the inequalities $W > 0$ and $h > 0$.
  For $W = 1$ the proportion is the root of $x^3 - 2 x^2 + x - 1$ in $[1, infinity)$, and the tiling is the sixth of @fig:three.
] <ex:plastic>

The inequalities of the system say only that tiles have positive size.
They do not say that a tile is narrower than its floor or lower than its wall, although the record presupposes it.
The next section shows that this is enough.

== Mosaic classes <sec:mosaic>

The system of a record does not depend on all the information in the record.
It depends only on which tiles border each maximal segment of the tiling, and not on the order in which the corners of tiles on the two sides of a segment alternate.

#definition(name: [mosaic class])[
  A _segment_ of a tiling is a maximal line segment contained in the union of the boundaries of the tiles and not contained in the boundary of the main rectangle, or one of the four sides of the main rectangle.
  Two tilings with $n$ tiles are _mosaic equivalent_ if their tiles can be numbered so that, for each side of each tile, the tiles whose opposite side lies on the same segment are the same in both, and the segments carrying the four sides of the main rectangle correspond.
] <def:mosaic>

Mosaic classes of tilings in which no four tiles meet at a point are the mosaic floorplans of the literature on rectangulations, which are counted by the Baxter numbers @ackerman2006 @chung1978; the finer classification that also records the alternation of corners along segments gives the generic rectangulations @reading2012.

In terms of electrical networks @bsst1940, each horizontal segment is a node, each tile is a resistor joining the segment that carries its top side to the one that carries its bottom side, the width of a tile is the current through it and its height the potential difference across it.
A wide tile has resistance $1 slash x$ and a tall one resistance $x$.
The equations of the system are Kirchhoff's laws for this network, which is determined by the mosaic class.

#proposition(name: [uniqueness])[
  Let $rho$ be a complete admissible record and let $x > 0$.
  The equations of the system of $rho$ have exactly one solution in $W, s_1, dots, s_k$.
  Consequently they have a unique solution over the field $QQ(x)$, and in it $W = N(x) slash D(x)$ for polynomials $N, D in ZZ[x]$ with $D(x) != 0$ for all real $x > 0$.
] <prop:unique>

#proof[
  #todo[proof by the energy identity: for two solutions with the same height, the difference of the two assignments of widths and heights satisfies all segment equations with total height zero, so the sum over tiles of width times height vanishes; as each term is the resistance times the square of the width, all widths vanish. To be written in full and aligned with the formal development.]
]

The uncovered region of a staircase can be extended by a tile of full height only along the floor of the previous tier, and two records that differ in whether tiles standing on a segment were placed before or after the tiles hanging below it describe mosaic equivalent tilings.
The search keeps one of the two orders.

#definition(name: [started floor])[
  In a sequence of placements, the floor of a tier is _started_ if the tier was created to the right of a tile placed inside, or by a full-height placement.
  An admissible sequence is _reduced_ if no tile of full height, and no full tile, is placed at a tier whose previous tier has a started floor.
] <def:started>

#proposition(name: [one record per class])[
  Every tiling in which no four tiles meet at a point is mosaic equivalent to a tiling whose canonical sequence is reduced, and the reduced sequences of mosaic equivalent tilings coincide up to the orientations of square tiles.
  The number of complete reduced admissible sequences of $n$ placements, disregarding orientations, is the Baxter number $B(n)$.
] <prop:baxter>

#proof[
  #todo[proof. The first statement: within a mosaic class the alternation of corners along each horizontal segment is free, and choosing the one in which all tiles above the segment begin to the right of all junctions below it yields a reduced canonical sequence. The count has been verified computationally for $n <= 13$ against @oeisA001181; a bijective proof, or a reference, is needed.]
]

Since the system depends only on the mosaic class, a solution of the system of a reduced record describes a tiling of that class even when the tiling itself, with its particular alternation of corners, has a canonical sequence that is not reduced.

#proposition(name: [soundness])[
  Let $rho$ be a complete reduced admissible record, and let $x >= 1$ and $W, s_1, dots, s_k$ satisfy the system of $rho$.
  Then $[0, W] times [0, 1]$ has a similar tiling of proportion $x$ with $n$ tiles, in which the $j$-th tile has the orientation and the size that $rho$ and the solution assign to it.
] <prop:sound>

#proof[
  #todo[proof, to be aligned with the formal development. Outline: by @prop:unique the solution is the unique flow of the network of the class with positive resistances; all currents are positive, and a planar network with positive currents is realised by a tiling @bsst1940.]
]

#proposition(name: [completeness])[
  Let $x >= 1$ and $W > 0$, and let $cal(T)$ be a similar tiling of $[0, W] times [0, 1]$ of proportion $x$ with $n$ tiles.
  Then there are a complete reduced admissible record $rho$ of $n$ placements and values $s_1, dots, s_k$ such that $x, W, s_1, dots, s_k$ satisfy the system of $rho$.
  If $W = 1$, the record can be chosen so that its first tile is wide.
] <prop:complete>

#proof[
  #todo[proof, to be aligned with the formal development. Outline: if no four tiles of $cal(T)$ meet at a point, take the reduced record of its class from @prop:baxter; the sizes of the tiles of $cal(T)$ satisfy the equations because these depend only on the class, and they are positive. A tiling in which four tiles meet at a point is a limit of tilings of a fixed class in which two junctions on a segment approach each other, and its sizes satisfy the system of that class. The last statement follows from @prop:transposition, as transposition fixes the bottom-left tile.]
]

== Solving the system <sec:solving>

By @prop:unique, the equations of a record determine the aspect ratio of the main rectangle as a rational function $R_rho (x) = N(x) slash D(x)$ of the proportion, and every tile size as a rational function with the same denominator.
For a main rectangle of aspect ratio $p slash q$, the proportions realised by the record are therefore the roots $alpha >= 1$ of
$ F_rho (x) := q N(x) - p D(x) $
at which all the size functions are positive.

The reference form of the search treats each record separately and uses exact arithmetic throughout.

+ The matrix of the equations, with entries in $ZZ[x]$ after clearing powers of $x$, is brought to triangular form by fraction-free elimination @bareiss1968, which yields $N$ and $D$.
+ The record is discarded if $F_rho$ has no root in $[1, infinity)$.
+ Otherwise $F_rho$ is factorised into irreducible factors over $ZZ$, and the real roots of each factor in $[1, infinity)$ are isolated by Descartes' rule of signs with bisection @collins1976.
  Each root is thereby identified by its minimal polynomial and its position among the roots of that polynomial.
+ Back-substitution gives each tile size as $Q_j (x) slash D(x)$ with $Q_j in ZZ[x]$.
+ For each root $alpha$, the signs of $D(alpha)$ and of each $Q_j (alpha)$ are determined exactly: $Q_j (alpha) = 0$ if and only if the minimal polynomial of $alpha$ divides $Q_j$, and otherwise the sign is found by evaluating $Q_j$ on an isolating interval for $alpha$, refined until the value is separated from zero.
  The root is accepted if all the signs are equal.

Factorisation proceeds by reduction modulo a prime exceeding twice the Landau–Mignotte bound on the coefficients of the factors, using Berlekamp's method @berlekamp1970, followed by recombination of the modular factors by trial division.

#proposition(name: [correctness of the reference search])[
  For integers $p, q >= 1$ and $n >= 1$, the set of real algebraic numbers accepted by the reference search over all complete reduced admissible records of $n$ placements, with the first tile wide if $p = q$, is $P_n (p slash q)$.
] <prop:reference>

#proof[
  By @prop:unique, for each record and each $x >= 1$ the equations have the unique solution given by the rational functions $N slash D$ and $Q_j slash D$, so the record realises $x$ with main aspect ratio $p slash q$ exactly when $F_rho (x) = 0$ and all $Q_j (x) slash D(x)$ are positive, which is what the search tests.
  The result follows from @prop:sound and @prop:complete.
]

The implementation does not rely on @prop:unique: it counts the records for which the elimination finds no pivot, for which $D$ vanishes at a candidate root, or for which $F_rho$ is identically zero.
All three counts were zero in every computation reported in @sec:results.

= Optimisations <sec:optimisations>

The reference search treats $2^(n - 1) B(n)$ records independently when the main rectangle is a square, each at the cost of a symbolic elimination.
The search actually used shares work between records with a common beginning, and replaces nearly all exact sign determinations by certified numerical ones.
Its cost is about $0.6$ microseconds of processor time per record.

== Eager elimination <sec:eager>

Records are explored depth first, as paths in the tree of admissible sequences, and the linear forms for floors and walls are maintained along the current path.
Instead of collecting equations to be solved at the leaves, each equation is used at once to eliminate one unknown from every floor and wall of the current staircase.

To keep the system homogeneous, the main rectangle is given sides $p t$ and $q t$ for an unknown scale $t > 0$.
A staircase with $m$ tiers then involves exactly $m - 1$ free unknowns besides $t$.

#definition(name: [elimination step])[
  Let $pi$ be a non-zero polynomial, the _current pivot_, initially $1$, and let the floors and walls of the current staircase be given by forms $Phi$ in the free unknowns and $t$ with coefficients in $ZZ[x, x^(-1)]$, such that the corresponding length is $Phi slash pi$.
  Let $E$ be the form of an equation $E = 0$ contributed by a full placement, and let $u$ be a free unknown whose coefficient $E_u$ in $E$ is not zero.
  The _elimination step_ replaces every form $Phi$ by
  $ Phi' := (E_u Phi - Phi_u E) / pi, $
  and the pivot by $E_u$.
  A tile placed inside after the step receives the form $pi u'$ for a new unknown $u'$, where $pi$ is the pivot current at that time.
] <def:elimination>

#proposition(name: [eager elimination])[
  In @def:elimination, the division is exact, the forms $Phi'$ do not involve $u$, and on the solutions of $E = 0$ with $E_u != 0$ the length $Phi' slash E_u$ equals the length $Phi slash pi$.
  After the last placement of a complete record, the equation contributed by that placement has the form $c(x) t = 0$, and $c$ is $F_rho$ up to sign and a power of $x$.
] <prop:eager>

#proof[
  #todo[proof: the forms are rows of a matrix undergoing Bareiss elimination with column pivoting, in which rows created after some steps are linear combinations, with coefficients that are powers of $x$, of rows that have undergone the same steps; exactness of the division is Sylvester's identity @bareiss1968. The last statement identifies the final coefficient with a maximal minor of the system.]
]

The cost of an elimination step is proportional to the square of the number of tiers, and most nodes of the search tree are close to the leaves, where staircases have one or two tiers.
The two orientations of the last tile give the polynomials $c_L - x c_M$ and $c_M - x c_L$, where $c_L t$ and $c_M t$ are the forms of the last floor and wall, without any further elimination.

The implementation performs the divisions with a check of exactness and with machine integers whose range is checked; a record for which either check fails, or for which no pivot exists, is passed to the reference search.

== Candidate roots <sec:candidates>

Different records often lead to the same polynomial: for a square and thirteen tiles, $2.8 times 10^11$ records lead to $2.6 times 10^8$ polynomials with a root in $[1, infinity)$.
A polynomial whose expansion in powers of $x - 1$ has non-negative coefficients and positive constant term has no such root and is discarded.
The roots of the others are obtained from a table shared by all threads, indexed by the coefficients, so that each polynomial is factorised once.

== Numerical verification <sec:numeric>

Let $alpha$ be a root of the final polynomial of a record, known through an enclosing interval of floating-point numbers of relative width about $10^(-15)$.
The tile sizes at $alpha$ are computed in interval arithmetic with outward rounding: the elimination steps along the path are undone in reverse order, each giving the eliminated unknown as a quotient of interval values, and the placements are then replayed on intervals.

#proposition(name: [numerical verification])[
  Let $alpha >= 1$ be a root of the final polynomial of a complete reduced admissible record, and suppose that the interval computation finds every pivot to be different from zero at $alpha$.
  If every tile size is enclosed in an interval of positive numbers, the record realises $alpha$.
  If some tile size is enclosed in an interval of non-positive numbers, it does not.
] <prop:numeric>

#proof[
  Since the pivots do not vanish at $alpha$, the elimination steps are equivalences at $x = alpha$ by @prop:eager, so the values recovered by back-substitution are the unique solution of the equations other than the last, and the last holds because $alpha$ is a root of the final polynomial.
  The intervals contain the exact tile sizes, so their signs decide the inequalities of the system.
]

The remaining case, in which the interval for some tile size contains zero, arises almost always because the size is exactly zero: the solution is then a tiling with fewer tiles, as for the pinwheel arrangement of five tiles, whose central tile degenerates to a point.
Such cases are about one in a hundred, and they are settled exactly without recourse to the reference search.

#proposition(name: [degenerate tiles])[
  Let $Phi$ be the form giving a side of a tile at the stage at which it was placed, and let $c(x) t$ be the form obtained by applying to $Phi$ the elimination steps that follow along the path.
  Let $alpha$ be a root of the final polynomial at which no pivot vanishes, with minimal polynomial $f$.
  Then the side vanishes at $alpha$ if and only if $f$ divides $c$.
] <prop:degenerate>

#proof[
  By @prop:eager the side equals $c(alpha) t slash pi(alpha)$ for the final pivot $pi$, with $t > 0$ and $pi(alpha) != 0$, and $c(alpha) = 0$ if and only if $f$ divides $c$ in $QQ[x]$.
]

A record with a tile of zero size is rejected.
If no doubtful size is exactly zero, or if a pivot cannot be separated from zero, the record is passed to the reference search; for ten tiles this happens for one record in ten thousand.

#proposition(name: [correctness of the search])[
  The search with eager elimination, candidate roots and numerical verification accepts the same algebraic numbers as the reference search.
] <prop:fast>

#proof[
  A record is decided either by the reference search or under the hypotheses of @prop:numeric and @prop:degenerate, and by @prop:eager its final polynomial has the same roots in $[1, infinity)$ as $F_rho$.
]

= Results <sec:results>

All computations were carried out with the Rust implementation of the search, on a machine with sixteen cores and 128 GB of memory.
In every run, no singular system and no arithmetic overflow was encountered, and no record had an aspect ratio independent of the proportion.

== The square <sec:square>

@tab:counts lists $a(n)$ for $n <= 13$, with the number of records examined, which is $2^(n - 1) B(n)$, the number of pairs of a record and a proportion that it realises, and the number of distinct polynomials with a root in $[1, infinity)$.

#figure(
  kind: table,
  datatable(csv("data/counts.csv")),
  caption: [Proportions for the square. A record is a reduced admissible sequence with orientations, the first tile being wide; a tiling is a record with a proportion that it realises.],
) <tab:counts>

The values for $n <= 8$ agree with those of Henderson and Gerbet, and the values for $n = 9$ and $n = 10$ agree with those reported by Einstein.
The values for $n = 11$, $12$ and $13$ are new.
Those for $n = 11$ and $n = 12$ were each computed twice, with the reference treatment of degenerate tiles and with that of @prop:degenerate, with identical results; the value for $n = 13$ was computed once and took three hours.

The search was checked in several further ways.
For $n <= 9$ the search of @sec:optimisations and the reference search of @sec:solving agree on every proportion and on the number of records realising it.
For $n = 7$ the distribution of the proportions by algebraic degree agrees with that derived from Henderson's published list.
For main rectangles of aspect ratios $w$ and $1 slash w$ the lists of proportions coincide, as @prop:transposition requires, although the search is not symmetric under transposition.

@fig:four shows one tiling for each of the eleven proportions with four tiles.
Several tilings may share a proportion without being related by a symmetry, as @ex:shared shows.

#figure(
  image("figures/four-tiles.svg", width: 92%),
  caption: [One tiling for each proportion achievable with four tiles.],
) <fig:four>

#example[
  For four tiles, the proportion $1.5436...$, the real root of $x^3 - 2 x^2 + 2 x - 2$, is realised by the six records of @fig:shared.
  In two of them a tall tile spans the height of the square, and in the other four a wide tile spans its width.
] <ex:shared>

#figure(
  image("figures/shared-cubic.svg", width: 92%),
  caption: [The six records with four tiles and first tile wide that realise the real root of $x^3 - 2 x^2 + 2 x - 2$.],
) <fig:shared>

== Algebraic degrees <sec:degrees>

Every proportion with $n$ tiles has degree at most $n$ @taams2023.
@tab:degrees and @tab:degrees-high give the number of proportions of each degree.

#figure(
  kind: table,
  datatable(csv("data/degrees.csv")),
  caption: [Number of proportions for the square, by algebraic degree from $1$ to $7$.],
) <tab:degrees>

#figure(
  kind: table,
  datatable(csv("data/degrees-high.csv")),
  caption: [Number of proportions for the square, by algebraic degree from $8$ to $13$.],
) <tab:degrees-high>

Odd degrees are markedly more frequent than the neighbouring even ones.
Degree $n$ is attained for every $n$ in the table other than $2$ and $4$.

The proportions of degree one are explained in part by dissections into squares.
If all tiles of a similar tiling of the square have the same orientation, stretching one axis by the proportion gives a dissection of a rectangle into $n$ squares, whose aspect ratio is the proportion.
The number of aspect ratios of rectangles that can be dissected into $n$ squares is entry A210517 of the OEIS @oeisA210517, which lists $1, 1, 2, 5, 11, 28, 74, 211$.
@tab:rational compares it with the number of rational proportions.

#figure(
  kind: table,
  datatable(csv("data/rational.csv")),
  caption: [Rational proportions for the square: their number, the number of those realised by tiles of a single orientation, and those realised with $n$ tiles only by tiles of both orientations.],
) <tab:rational>

The rational proportions that require both orientations were identified by searching, for each rational proportion $p slash q$ found with $n$ tiles, for a dissection of the $p times q$ rectangle into $n$ squares.
For instance, a rectangle of sides $2$ and $1$ cannot be dissected into six squares, but the square can be dissected into six rectangles of proportion $2$, some wide and some tall.

== Other main rectangles <sec:rectangles>

@tab:rectangles lists $a_w (n)$ for a few rational aspect ratios and $n <= 9$.

#figure(
  kind: table,
  datatable(csv("data/rectangles.csv")),
  caption: [Number of proportions for main rectangles of aspect ratio $w$.],
) <tab:rectangles>

== Structure of the sequence <sec:structure>

#todo[closed or simplified forms for $a(n)$ or for related counts, with their proofs, and conjectures supported by the computed evidence; pending the analysis in progress.]

#bibliography("refs.bib", style: "ieee")

#show: appendix

= Catalogue of tilings <app:catalogue>

@fig:five and @fig:six show one tiling for each proportion achievable with five and with six tiles, labelled by proportion; the cases of three and four tiles are in @fig:three and @fig:four.
The tiling shown for a proportion is the first that the search found, and is in general one of several.

#figure(
  image("figures/five-tiles.svg", width: 100%),
  caption: [One tiling for each of the $51$ proportions achievable with five tiles.],
) <fig:five>

#figure(
  image("figures/six-tiles.svg", width: 100%),
  caption: [One tiling for each of the $245$ proportions achievable with six tiles.],
) <fig:six>

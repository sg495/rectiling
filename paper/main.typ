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
@sec:search presents the search procedure, with the propositions that make it sound and complete.
@sec:optimisations presents the optimisations that make thirteen tiles feasible, with the propositions that justify them.
@sec:results reports the results.
Soundness and completeness of the reference search have been formalised in Lean 4 with Mathlib, taking as hypotheses the specifications of the exact-arithmetic routines; #todo[extend this statement to the optimised search once its formalisation is complete, and cite the development.]

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

The sets $P_n (w)$ are finite in every case treated in this paper, as a by-product of the computation; see @sec:solving.

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
The proof singles out, at each stage, the first tier whose tile fits.

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

== Placement rules <sec:rules>

A tiling generally admits several orderings as in @prop:construction, and tilings that differ only in how the corners of their tiles alternate along a segment will turn out to impose the same conditions on the sizes of the tiles.
The search therefore restricts the sequences of placements by two rules.
Each placement is recorded as a triple of the index of the tier, the fit, and the orientation of the tile, wide or tall; a _record_ is a sequence of such triples, and it is _complete_ if it leads from the staircase of the main rectangle to the empty staircase.

#definition(name: [admissible record])[
  Along a record, a tier becomes _stale_ when a tile is placed at a tier of larger index; it ceases to be stale when its floor is lengthened, and when a tile is placed at it.
  The floor of a tier is _started_ if the tier was created to the right of a tile placed inside, or if its anchor was moved by a placement of full height; it ceases to be started when a tile of full width is placed at the tier.
  A record is _admissible_ if no tile is placed at a stale tier, and no tile of full height and no full tile is placed at a tier whose previous tier has a started floor.
] <def:admissible>

The first rule fixes the order in which tiles at different tiers are placed.
The second concerns a horizontal segment that carries the tops of some tiles and the bottoms of others: a floor is started when a tile already stands on its segment to the left, and the rule forbids lengthening such a floor from below, so that the tiles standing on a segment are placed only after all the tiles hanging below it.

== The linear system <sec:system>

Fix a complete admissible record of $n$ placements.
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
  The _system_ of $rho$ consists of one equation for each full placement, $L = x M$ for a wide tile and $M = x L$ for a tall one, where $L$ and $M$ are the floor and wall of its tier, together with one strict inequality for each placement: the short side is positive for an inside tile, the wall is positive for a tile of full height, and the floor is positive for a tile of full width and for a full tile.
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

== Soundness and completeness <sec:correct>

The inequalities of the system say only that tiles have positive size.
They do not say that a tile is narrower than its floor or lower than its wall, although its fit presupposes it.
For admissible records this follows from the two rules, which are thus needed for every solution to be a tiling, and not only to avoid repetitions.

#proposition(name: [soundness])[
  Let $rho$ be a complete admissible record of $n$ placements, and let $x >= 1$ and $W, s_1, dots, s_k$ satisfy the system of $rho$.
  Then the rectangles that $rho$ and the solution assign to the placements form a similar tiling of $[0, W] times [0, 1]$ of proportion $x$ with $n$ tiles.
] <prop:sound>

#proof[
  #todo[to be written out from the formal proof. Outline: it suffices that every floor and wall arising along $rho$ is positive, since the tiles then fit their tiers and each placement removes a rectangle from the uncovered region. If a floor becomes non-positive, it does so to the right of a tile placed with a narrow fit, so it is started, or it is the floor of the last tier; a floor that is non-positive and started or last remains so under every admissible placement with positive tiles, because it can be lengthened only from below, which the second rule forbids, and its tier can be removed only by a tile whose width is that floor. Similarly a wall that becomes non-positive lies behind tiers made stale by the placement that shortened it, and remains non-positive as long as they are stale. In either case the staircase cannot become empty.]
]

For completeness, the tiles of a given tiling must be ordered so that both rules are obeyed.
The order that places the tile at the first tier at which it fits, as in the proof of @prop:construction, does not always obey the second rule.
The following one does.

#definition(name: [extending floor])[
  Let $cal(T)$ be a tiling and let $S$ be a staircase whose uncovered region is a union of tiles of $cal(T)$.
  The floor of a tier of $S$, with right end at $(c, d)$, _extends_ in $cal(T)$ if some tile of $cal(T)$ has its top side at height $d$, over an interval $[u, v]$ with $u <= c < v$.
] <def:extends>

The floor extends when the segment that carries it continues to the right beyond its end, so that a tile of full height placed at the next tier will lengthen it.

#proposition(name: [completeness])[
  Let $x >= 1$, $W > 0$ and $H > 0$, and let $cal(T)$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$ with $n$ tiles.
  Then there are a complete admissible record $rho$ of $n$ placements, in which each placement has the orientation of the tile it places, and values of the free sides, such that the system of $rho$ is satisfied and the tiles assigned to the placements are those of $cal(T)$.
  If $W = H$, then $cal(T)$ or its transpose arises from such a record whose first tile is wide.
] <prop:complete>

#proof[
  #todo[to be written out from the formal proof. Outline: at each stage, place the tile at the anchor of the first tier whose floor does not extend. Such a tier exists, since the floor of the last tier ends on the right side of the main rectangle; the tile at its anchor fits it, by the argument of @prop:construction applied to the tiers before it, whose floors extend. Two invariants hold along the construction: the floor of a stale tier extends, and a started floor does not. Hence the tier chosen is not stale, and a tile of full height is placed only when the floor of the previous tier extends, so that it is not started. The last statement follows from @prop:transposition, as transposition fixes the bottom-left tile.]
]

A square tile is both wide and tall, so that a tiling with square tiles arises from several records; this multiplicity is harmless, since only proportions are counted.

== Mosaic classes <sec:mosaic>

The system of a record depends only on which tiles border each maximal segment of the tiling, and not on the order in which the corners of tiles on the two sides of a segment alternate.

#definition(name: [mosaic class])[
  A _segment_ of a tiling is a maximal line segment contained in the union of the boundaries of the tiles and not contained in the boundary of the main rectangle, or one of the four sides of the main rectangle.
  Two tilings with $n$ tiles are _mosaic equivalent_ if their tiles can be numbered so that, for each side of each tile, the tiles whose opposite side lies on the same segment are the same in both, and the segments carrying the four sides of the main rectangle correspond.
] <def:mosaic>

Mosaic classes of tilings in which no four tiles meet at a point are the mosaic floorplans of the literature on rectangulations, which are counted by the Baxter numbers $B(n)$ @ackerman2006 @chung1978; the finer classification that also records the alternation of corners along segments gives the generic rectangulations @reading2012.
The staircase construction never distinguishes the order of corners along a vertical segment, and the rule on started floors fixes it along horizontal ones.
Accordingly, for every $n <= 13$ the number of complete admissible sequences of $n$ placements, disregarding orientations, is $B(n)$ @oeisA001181.
We have not proved that each mosaic class has exactly one such sequence; the correctness of the search does not depend on it.

In terms of electrical networks @bsst1940, each horizontal segment is a node, each tile is a resistor joining the segment that carries its top side to the one that carries its bottom side, the width of a tile is the current through it and its height the potential difference across it.
A wide tile has resistance $1 slash x$ and a tall one resistance $x$.
The equations of the system are Kirchhoff's laws for this network, which is determined by the mosaic class, and for positive resistances these determine the currents.
One therefore expects the equations of every record to have exactly one solution for each $x > 0$.
The search does not rely on this expectation, but verifies it for each record, in the following form.

#definition(name: [regular record])[
  Let $rho$ be a complete admissible record and let $p, q >= 1$ be integers.
  Write the equations of the system of $rho$ as $A (s_1, dots, s_k, W)^top = c$, with $A$ a square matrix and $c$ a vector over $ZZ[x]$, after clearing powers of $x$.
  The record is _regular_ for the aspect ratio $p slash q$ if $det A != 0$; if, for the solution $W = N slash D$ over $QQ(x)$ given by Cramer's rule with $D = det A$, the polynomial $F_rho := q N - p D$ is not zero; and if $D(alpha) != 0$ for every root $alpha >= 1$ of $F_rho$.
] <def:regular>

== Solving the system <sec:solving>

For a regular record, the proportions realised with main aspect ratio $p slash q$ are the roots $alpha >= 1$ of $F_rho$ at which all the tile sizes, which are rational functions $Q_j slash D$ of the proportion, are positive.
The reference form of the search treats each record separately and uses exact arithmetic throughout.

+ The matrix of the equations is brought to triangular form by fraction-free elimination @bareiss1968, which yields $N$ and $D$.
+ The record is discarded if $F_rho$ has no root in $[1, infinity)$.
+ Otherwise $F_rho$ is factorised into irreducible factors over $ZZ$, and the real roots of each factor in $[1, infinity)$ are isolated by Descartes' rule of signs with bisection @collins1976.
  Each root is thereby identified by its minimal polynomial and its position among the roots of that polynomial.
+ Back-substitution gives each tile size as $Q_j (x) slash D(x)$ with $Q_j in ZZ[x]$.
+ For each root $alpha$, the signs of $D(alpha)$ and of each $Q_j (alpha)$ are determined exactly: $Q_j (alpha) = 0$ if and only if the minimal polynomial of $alpha$ divides $Q_j$, and otherwise the sign is found by evaluating $Q_j$ on an isolating interval for $alpha$, refined until the value is separated from zero.
  The root is accepted if all the signs are equal.

Factorisation proceeds by reduction modulo a prime exceeding twice the Landau–Mignotte bound on the coefficients of the factors, using Berlekamp's method @berlekamp1970, followed by recombination of the modular factors by trial division.

#proposition(name: [correctness of the reference search])[
  Let $p, q >= 1$ and $n >= 1$ be integers, and consider the reference search over all complete admissible records of $n$ placements, with the first tile wide if $p = q$.
  Every number that it accepts belongs to $P_n (p slash q)$.
  If every such record is regular for $p slash q$, the numbers accepted are exactly the elements of $P_n (p slash q)$.
] <prop:reference>

#proof[
  If $alpha$ is accepted for a record, then $D(alpha) != 0$ and the values $Q_j (alpha) slash D(alpha)$ and $W = p slash q$ satisfy the system at $x = alpha$, so $alpha in P_n (p slash q)$ by @prop:sound.
  Conversely, let $alpha in P_n (p slash q)$.
  By @prop:complete some record, with first tile wide if $p = q$, has a system satisfied at $x = alpha$ with $W = p slash q$.
  If the record is regular, the solution at $x = alpha$ is the one given by Cramer's rule, so $F_rho (alpha) = 0$ and the tile sizes are $Q_j (alpha) slash D(alpha) > 0$, and $alpha$ is accepted.
]

The implementation counts the records for which the elimination finds no pivot, for which $D$ vanishes at a candidate root, or for which $F_rho$ is identically zero.
All three counts were zero in every computation reported in @sec:results, so that every record examined was regular.
In particular the sets $P_n (w)$ computed there are finite.

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
  Let $alpha >= 1$ be a root of the final polynomial of a complete admissible record, and suppose that the interval computation finds every pivot to be different from zero at $alpha$.
  If every tile size is enclosed in an interval of positive numbers, the record realises $alpha$.
  If some tile size is enclosed in an interval of non-positive numbers, it does not.
] <prop:numeric>

#proof[
  Since the pivots do not vanish at $alpha$, the elimination steps are equivalences at $x = alpha$ by @prop:eager, so the values recovered by back-substitution are the only solution of the equations other than the last, and the last holds because $alpha$ is a root of the final polynomial.
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
  If every record is regular, the search with eager elimination, candidate roots and numerical verification accepts the same algebraic numbers as the reference search.
] <prop:fast>

#proof[
  A record is decided either by the reference search or under the hypotheses of @prop:numeric and @prop:degenerate, and by @prop:eager its final polynomial has the same roots in $[1, infinity)$ as $F_rho$.
]

= Results <sec:results>

All computations were carried out with the Rust implementation of the search, on a machine with sixteen cores and 128 GB of memory.
In every run, every record was regular in the sense of @def:regular, and no arithmetic overflow was encountered.

== The square <sec:square>

@tab:counts lists $a(n)$ for $n <= 13$, with the number of records examined, which is $2^(n - 1) B(n)$, the number of pairs of a record and a proportion that it realises, and the number of distinct polynomials with a root in $[1, infinity)$.

#figure(
  kind: table,
  datatable(csv("data/counts.csv")),
  caption: [Proportions for the square. A record is an admissible sequence with orientations, the first tile being wide; a tiling is a record with a proportion that it realises.],
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
Degree $n$ is attained for every $n$ in the table other than $2$ and $4$; the proportions of degree $n$ for $n <= 7$ are shown in @app:full.

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

= Proportions of full degree <app:full>

A proportion achievable with $n$ tiles has algebraic degree at most $n$.
@fig:full shows one tiling for each proportion of degree exactly $n$ with $n <= 7$ tiles, and @tab:full lists their minimal polynomials, with the number of records that realise each.
There is one such proportion for three tiles, none for four, four for five, two for six and $44$ for seven.

#figure(
  image("figures/full-degree.svg", width: 100%),
  caption: [One tiling for each proportion whose degree equals the number $n$ of tiles, for $n <= 7$.],
) <fig:full>

#figure(
  kind: table,
  datatable(csv("data/full-degree.csv"), size: 0.85em),
  caption: [The proportions of degree $n$ achievable with $n <= 7$ tiles.],
) <tab:full>

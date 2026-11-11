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

We work in the real plane with axis-parallel rectangles.
A rectangle is given by its bottom-left corner and its two side lengths, and its proportion disregards which side is the longer.

#definition(name: [rectangle])[
  A _rectangle_ is a quadruple $R = (a, b, w, h)$ of real numbers with $w, h > 0$, which stands for the set $[a, a + w] times [b, b + h]$; its _corner_ is the point $(a, b)$, its _width_ is $w$, its _height_ is $h$, and its _interior_ is $(a, a + w) times (b, b + h)$.
  For a real number $x >= 1$, the rectangle $R$ has _proportion_ $x$ if $w = x h$ or $h = x w$; in the first case it is _wide_ for $x$, and in the second it is _tall_ for $x$.
] <def:rectangle>

Since the sides are positive and $x >= 1$, a rectangle has proportion $x$ exactly when $x = max(w slash h, h slash w)$, and it is both wide and tall exactly when it is a square and $x = 1$.
A tiling is a dissection in the usual sense: the tiles cover the main rectangle and overlap only along their boundaries.

#definition(name: [tiling])[
  A _tiling_ of a rectangle $M$ is a finite sequence $R_1, dots, R_n$ of rectangles, its _tiles_, whose union is $M$ and whose interiors are pairwise disjoint.
  For $x >= 1$, a tiling is _similar of proportion $x$_ if every tile has proportion $x$.
] <def:tiling>

The order of the tiles plays no part: every rearrangement of a tiling is a tiling, and the tiles of a tiling are pairwise distinct, because a rectangle meets its own interior.
Two rectangles with disjoint interiors are separated by a horizontal or a vertical line, so that the interior of each misses the other altogether; conversely, two tiles of a tiling whose interiors meet are equal.
Both remarks are used repeatedly below.

#definition(name: [achievable proportions])[
  For real numbers $W, H > 0$ and an integer $n >= 0$, let $P_n (W, H)$ be the set of those $x >= 1$ for which the rectangle $[0, W] times [0, H]$ has a similar tiling of proportion $x$ with exactly $n$ tiles.
  We write $P_n (w) := P_n (w, 1)$, $a_w (n) := |P_n (w)|$ and $a(n) := a_1 (n)$.
] <def:counts>

The sets $P_n (w)$ are finite in every case treated in this paper, as a by-product of the computation; see @sec:solving.
Three elementary observations are used throughout.
The first is that scaling the plane preserves proportions, so that only the aspect ratio of the main rectangle matters.

#proposition(name: [scaling])[
  For all $W, H, c > 0$ and $n >= 0$, $P_n (c W, c H) = P_n (W, H)$.
] <prop:scaling>

#proof[
  Let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and replace each tile $(a, b, w, h)$ by $(c a, c b, c w, c h)$.
  The new sides are positive, and $c w = x c h$ if $w = x h$, and likewise with the sides exchanged, so the new tiles have proportion $x$.
  A point $p$ lies in a new tile, or in its interior, exactly when $p slash c$ lies in the old one, or in its interior; hence the new tiles cover $[0, c W] times [0, c H]$ exactly and have pairwise disjoint interiors.
  This shows that $P_n (W, H) subset.eq P_n (c W, c H)$, and the same statement for the rectangle $[0, c W] times [0, c H]$ and the factor $1 slash c$ gives the other inclusion.
]

The second is that exchanging the two axes turns a tiling of a rectangle into a tiling of the rectangle with the sides exchanged, turning wide tiles into tall ones.

#proposition(name: [transposition])[
  For all $W, H > 0$ and $n >= 0$, $P_n (W, H) = P_n (H, W)$.
  Consequently $P_n (w) = P_n (1 slash w)$ for all $w > 0$.
] <prop:transposition>

#proof[
  Let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and replace each tile $(a, b, w, h)$ by its _transpose_ $(b, a, h, w)$.
  The transpose has positive sides and proportion $x$, the two conditions $w = x h$ and $h = x w$ being exchanged.
  A point $(u, v)$ lies in the transpose of a tile, or in its interior, exactly when $(v, u)$ lies in the tile, or in its interior; hence the transposes cover $[0, H] times [0, W]$ exactly and have pairwise disjoint interiors.
  This gives $P_n (W, H) subset.eq P_n (H, W)$, and the other inclusion is the same statement with $W$ and $H$ exchanged.
  Finally $P_n (w) = P_n (w, 1) = P_n (1, w) = P_n (1 slash w, 1)$, the last equality by @prop:scaling with $c = 1 slash w$.
]

The third is that the sets of proportions grow with $n$ along steps of three.
Whether they grow along steps of one is not known to us.

#proposition(name: [subdivision])[
  For all $W, H > 0$ and $n >= 0$, $P_n (W, H) subset.eq P_(n + 3) (W, H)$.
] <prop:subdivision>

#proof[
  Let $R_1, dots, R_n$ be a similar tiling of $M = [0, W] times [0, H]$ of proportion $x$.
  The corner of $M$ lies in some tile, so $n >= 1$.
  Let $R_1 = (a, b, w, h)$, and let $Q_1, dots, Q_4$ be the rectangles of width $w slash 2$ and height $h slash 2$ with corners $(a, b)$, $(a + w slash 2, b)$, $(a, b + h slash 2)$ and $(a + w slash 2, b + h slash 2)$.
  They have proportion $x$, since $w slash 2 = x h slash 2$ if $w = x h$ and likewise with the sides exchanged.
  They form a tiling of $R_1$: the two with the same ordinate of the corner are separated by the line of abscissa $a + w slash 2$ and cover a rectangle of width $w$ and height $h slash 2$, and the two rectangles so obtained are separated by the line of ordinate $b + h slash 2$ and cover $R_1$.
  The sequence $Q_1, dots, Q_4, R_2, dots, R_n$ is then a tiling of $M$: its union is that of the original tiles, the interiors of the $Q_i$ are pairwise disjoint, and each of them lies in the interior of $R_1$, which is disjoint from the interiors of $R_2, dots, R_n$.
  It has $n + 3$ tiles of proportion $x$.
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

In the search the lengths of the steps of the staircase are not numbers but expressions in unknown quantities, and nothing guarantees beforehand that they take positive values.
The staircase is therefore defined first as a combinatorial object carrying lengths of an arbitrary kind, and its geometric reading is defined afterwards.

#definition(name: [staircase])[
  An _arithmetic of lengths_ is a set $cal(L)$ with two binary operations, written $ell + ell'$ and $ell - ell'$, and two unary operations, written $x ell$ and $ell slash x$.
  A _tier_ over $cal(L)$ consists of a _floor_ $L in cal(L)$, a _wall_ $M in cal(L)$ and two flags, _stale_ and _started_, each of which is set or clear.
  A _staircase_ over $cal(L)$ is a finite sequence $T_0, dots, T_(m - 1)$ of tiers over $cal(L)$, with $m >= 0$.
  The _initial staircase_ of $W, H in cal(L)$ consists of a single tier with floor $W$, wall $H$ and both flags clear.
  A map $f$ from an arithmetic of lengths to another is a _homomorphism_ if it commutes with the four operations; the _image_ of a staircase under $f$ is obtained by applying $f$ to every floor and wall, keeping the flags.
] <def:staircase>

Three arithmetics of lengths occur.
The first is the set of real numbers with the usual operations, for a fixed real number $x > 0$; a staircase over it is a _real staircase_.
The second has a single element, so that a staircase over it, a _bare staircase_, carries only the number of its tiers and their flags; every arithmetic of lengths has exactly one map to it, which is a homomorphism.
The others consist of linear forms in unknown lengths, and are introduced in @sec:solving and @sec:eager.

A real staircase is read geometrically inside a main rectangle $[0, W] times [0, H]$, the floors being laid end to end from the right side leftwards and the walls from the top side downwards.

#definition(name: [anchors and region])[
  Let $S = (T_0, dots, T_(m - 1))$ be a real staircase, with floors $L_i$ and walls $M_i$, and let $W$ and $H$ be real numbers.
  The _anchor_ of the tier $T_i$ is the point $(a_i, b_i)$ with
  $ a_i := W - sum_(j >= i) L_j, quad b_i := H - sum_(j <= i) M_j, $
  its _strip_ is the set of points $(u, v)$ with $a_i <= u <= W$ and $b_i <= v <= b_i + M_i$, and the _region_ $U(S)$ of the staircase is the union of the strips of its tiers.
  The staircase is _positive_ if all its floors and walls are positive.
] <def:region>

By definition $a_(i + 1) = a_i + L_i$ and $b_(i - 1) = b_i + M_i$, with the conventions $a_m := W$ and $b_(-1) := H$: the floor of a tier runs from its anchor to the next anchor, or to the right side of the main rectangle, and its wall runs from its anchor up to the level of the previous anchor, or to the top side.
The region of the initial staircase of $W$ and $H$ is the main rectangle $[0, W] times [0, H]$, and the region of the empty staircase is empty.
@fig:staircase shows a positive staircase with four tiers.

#figure(
  image("figures/staircase.svg", width: 38%),
  caption: [A partial tiling and its staircase. Anchors are circled, tiers are outlined, and the hatched part of each tier is the region within which a tile placed at its anchor must fit.],
) <fig:staircase>

A tile placed at the anchor of a tier may or may not be as wide as the floor, and may or may not be as high as the wall.
This gives four kinds of placement, each of which turns a staircase into another.
A tile that is as high as the wall has its height determined by the staircase, and its width by its orientation; a tile that is as wide as the floor is treated symmetrically; a tile that is neither has one side free.

#definition(name: [placement])[
  A _placement_ is a triple $p = (i, phi, o)$ of the index $i >= 0$ of a tier, a _fit_ $phi$, which is _inside_, _full height_, _full width_ or _full_, and an _orientation_ $o$, which is _wide_ or _tall_.
  A fit is _narrow_ if it is inside or full height, and _low_ if it is inside or full width.
  Let $S = (T_0, dots, T_(m - 1))$ be a staircase over $cal(L)$ with $i < m$, let $L$ and $M$ be the floor and the wall of $T_i$, and let $s in cal(L)$, the _free side_.
  The _size_ $(w, h)$ of the tile of $p$ is
  $ (w, h) := cases(
    (x s, s) & "if" phi "is inside and" o "is wide,",
    (s, x s) & "if" phi "is inside and" o "is tall,",
    (x M, M) & "if" phi "is full height and" o "is wide,",
    (M slash x, M) & "if" phi "is full height and" o "is tall,",
    (L, L slash x) & "if" phi "is full width and" o "is wide,",
    (L, x L) & "if" phi "is full width and" o "is tall,",
    (L, M) & "if" phi "is full.",
  ) $
  The _positive quantity_ of $p$ is $s$ if $phi$ is inside, $M$ if $phi$ is full height, and $L$ if $phi$ is full width or full.
  If $phi$ is full, the _equation_ of $p$ is the length $L - x M$ if $o$ is wide and $M - x L$ if $o$ is tall; other placements have no equation.
  _Placing_ $p$ on $S$ with free side $s$ gives the staircase $S'$ obtained as follows.
  + Every tier before $T_i$ becomes stale; if $phi$ is not low and $i > 0$, the floor $L_(i - 1)$ of $T_(i - 1)$ is then replaced by $L_(i - 1) + w$ and its stale flag is cleared.
  + The tier $T_i$ is replaced by two tiers if $phi$ is inside, the first with floor $w$, wall $M - h$ and both flags clear, the second with floor $L - w$, wall $h$, stale flag clear and started flag set; by one tier with floor $L - w$, wall $M$, stale flag clear and started flag set if $phi$ is full height; by one tier with floor $L$, wall $M - h$ and both flags clear if $phi$ is full width; and by nothing if $phi$ is full.
  + The tiers after $T_i$ are kept, except that, if $phi$ is not narrow and $i + 1 < m$, the wall $M_(i + 1)$ of $T_(i + 1)$ is replaced by $M_(i + 1) + h$.
  If $S$ is a real staircase, read in the main rectangle $[0, W] times [0, H]$, the _tile_ of $p$ is the quadruple $(a_i, b_i, w, h)$, where $(a_i, b_i)$ is the anchor of $T_i$.
  A placement with $i >= m$, at a tier that does not exist, leaves the staircase unchanged and has no positive quantity, no equation and no tile.
] <def:placement>

Only an inside placement makes use of the free side.
If $phi$ is not narrow then $w = L$, and if $phi$ is not low then $h = M$, by the definition of the size.
In geometric terms, an inside placement replaces the anchor by two, one above the tile and one to its right; a full-height placement moves the anchor to the right and lengthens the floor of the previous tier by $w$; a full-width placement moves the anchor up and heightens the wall of the next tier by $h$; and a full placement removes the anchor, lengthening the floor of the previous tier by $L$ and heightening the wall of the next by $M$.
The number of tiers thus increases by one with an inside placement, decreases by one with a full placement, and is unchanged otherwise.
Placing commutes with homomorphisms: if $f$ is a homomorphism, the image under $f$ of the staircase obtained by placing $p$ on $S$ with free side $s$ is obtained by placing $p$ on the image of $S$ with free side $f(s)$, and the positive quantity and the equation of $p$ on the image of $S$ are the images of those on $S$.
In particular, the number of tiers and the flags of the staircases obtained by successive placements do not depend on the arithmetic of lengths or on the free sides: they are those of the bare staircases obtained by the same placements.

== Placement rules <sec:rules>

A tiling generally admits several orderings in which its tiles can be placed, and tilings that differ only in how the corners of their tiles alternate along a segment will turn out to impose the same conditions on the sizes of the tiles.
The search therefore restricts the sequences of placements by two rules, which are expressed by the two flags, and abandons a sequence when fewer tiles remain to be placed than there are tiers.

#definition(name: [admissible record])[
  A placement $p = (i, phi, o)$ is _allowed_ at a staircase $S = (T_0, dots, T_(m - 1))$ if $i < m$, the tier $T_i$ is not stale and, in case $phi$ is not low and $i > 0$, the tier $T_(i - 1)$ is not started.
  It is _admissible_ at $S$ with $r$ tiles remaining if it is allowed at $S$, $r >= 1$, and the number $m'$ of tiers after the placement satisfies $m' <= r - 1$, and $m' = 0$ only if $r = 1$.
  A _record_ is a finite sequence $rho = (p_1, dots, p_ell)$ of placements.
  Given a sequence $s_1, s_2, dots$ of free sides, _placing_ $rho$ on a staircase $S$ means placing $p_1, dots, p_ell$ in turn, the $j$-th inside placement of $rho$ being made with free side $s_j$.
  The record $rho$ _obeys the rules_ from $S$ if each of its placements is allowed at the staircase on which it is placed and the staircase left by the last one is empty.
  The record $rho$ is _complete admissible for $n$ tiles_ if, on the bare initial staircase, each placement $p_j$ is admissible, with $n - j + 1$ tiles remaining, at the staircase on which it is placed, and the staircase left by the last one is empty.
  The _first tile is wide_ in $rho$ if $rho$ is empty or $p_1$ is wide.
] <def:admissible>

Whether a record obeys the rules from a staircase depends only on the flags, hence only on the bare staircase underlying it.
The first rule fixes the order in which tiles at different tiers are placed: a tier becomes stale when a tile is placed at a tier of larger index, and ceases to be stale when its floor is lengthened or a tile is placed at it.
The second concerns a horizontal segment that carries the tops of some tiles and the bottoms of others: a floor is started when a tile already stands on its segment to the left, and the rule forbids lengthening such a floor from below, so that the tiles standing on a segment are placed only after all the tiles hanging below it.
The bound on the number of tiers, by which the search abandons partial records, excludes nothing.

#proposition(name: [the bound on tiers])[
  A record is complete admissible for $n$ tiles if and only if it consists of $n$ placements and obeys the rules from the bare initial staircase.
] <prop:bound>

#proof[
  No placement is allowed at the empty staircase, so that in a record that obeys the rules no placement follows one that leaves the staircase empty.
  Suppose that $rho = (p_1, dots, p_ell)$ obeys the rules from a bare staircase $S$ with $m$ tiers.
  We show, by induction on $ell$, that $m <= ell$ and that each $p_j$ is admissible, with $ell - j + 1$ tiles remaining, at the staircase on which it is placed.
  If $ell = 0$ then $S$ is empty and there is nothing to prove.
  Otherwise let $S'$, with $m'$ tiers, be the staircase after $p_1$; then $m <= m' + 1$, the remaining placements obey the rules from $S'$, and by induction $m' <= ell - 1$ and the remaining placements are admissible as stated.
  Hence $m <= ell$, and $p_1$ is admissible with $ell$ tiles remaining: it is allowed, $ell >= 1$, $m' <= ell - 1$, and if $m' = 0$ then no placement follows $p_1$, so that $ell = 1$.
  Applied to the bare initial staircase, this shows that a record of $n$ placements that obeys the rules is complete admissible for $n$ tiles.
  Conversely, an admissible placement is allowed, so a record that is complete admissible for $n$ tiles obeys the rules from the bare initial staircase, and it remains to see that it has $n$ placements.
  More generally, if each placement $p_j$ of $rho$ is admissible, with $r - j + 1$ tiles remaining, on a staircase $S$ that is not empty, and the staircase left by the last one is empty, then $ell = r$, by induction on $ell$.
  Indeed $ell >= 1$; if the staircase after $p_1$ is empty then $r = 1$ by admissibility and no placement follows, so that $ell = 1$; otherwise $ell - 1 = r - 1$ by induction.
]

== The linear system <sec:system>

A record constrains the sizes of the tiles, and the constraints are linear once the proportion is fixed.
The short side of each tile placed inside its tier is a free unknown, and every other length is determined by the width and the height of the main rectangle and by these unknowns.

#definition(name: [constraints of a record])[
  Let $rho$ be a record, let $x > 0$, $W$ and $H$ be real numbers, and let $s = (s_1, s_2, dots)$ be a sequence of real numbers.
  Place $rho$ on the real initial staircase of $W$ and $H$ with the free sides $s$.
  The _positivity constraints_ of $rho$ are the positive quantities of its placements, one for each placement, and its _equations_ are the equations of its full placements, each taken on the staircase on which the placement is made.
  The data $(W, H, s)$ _satisfy the constraints of $rho$ at $x$_ if every positivity constraint is a positive number and every equation is zero.
  The _tiles of $rho$_ for $(x, W, H, s)$ are the tiles of its placements, in order, read in the main rectangle $[0, W] times [0, H]$.
] <def:system>

The constraints depend only on those free sides that are used, namely $s_1, dots, s_k$ if $rho$ has $k$ inside placements.
The unknowns are thus $W$, $H$ and $s_1, dots, s_k$, of which $W$ and $H$ will be given up to a common factor, and the following count shows that a complete record has as many equations as unknowns that remain.

#proposition(name: [number of equations])[
  A record with $k$ inside placements that obeys the rules from a staircase with $m$ tiers has $k + m$ full placements.
  In particular a complete admissible record with $k$ inside placements has $k + 1$ equations.
] <prop:count>

#proof[
  Each placement of the record is made at a tier that exists, so the number of tiers increases by one with each inside placement, decreases by one with each full placement, and is otherwise unchanged.
  It passes from $m$ to zero, so the number of full placements exceeds the number of inside placements by $m$.
  The second statement follows from @prop:bound, the initial staircase having one tier.
]

#example[
  Consider the record that places a wide tile of full width, then a tall tile of full height, then a wide full tile, all at tier $0$, with $H = 1$.
  The first tile has width $W$ and height $W slash x$, leaving a tier of floor $W$ and wall $1 - W slash x$.
  The second has that wall as its height $h$ and width $h slash x$, and the third has width $W - h slash x$ and height $h$, so the only equation is $W - h slash x - x h = 0$ with $h = 1 - W slash x$, that is,
  $ W = (x^3 + x) / (2 x^2 + 1), $
  and the positivity constraints are $W > 0$, $h > 0$ and $W - h slash x > 0$.
  For $W = 1$ the proportion is the root of $x^3 - 2 x^2 + x - 1$ in $[1, infinity)$, and the tiling is the sixth of @fig:three.
] <ex:plastic>

== Soundness <sec:sound>

The positivity constraints say only that tiles have positive size.
They do not say that a tile is narrower than its floor or lower than its wall, although its fit presupposes it.
For records that obey the rules this follows from the rules themselves, which are thus needed for every solution to be a tiling, and not only to avoid repetitions.
The argument has two parts.
The first is geometric: on a positive staircase, a tile that fits its tier as its fit says is cut out of the region.

#proposition(name: [effect of a placement])[
  Let $S$ be a positive real staircase, read in the main rectangle $[0, W] times [0, H]$, and let $p = (i, phi, o)$ be a placement at a tier $T_i$ of $S$, with floor $L$ and wall $M$, whose tile has size $(w, h)$ with $w, h > 0$.
  Suppose that $w < L$ if $phi$ is narrow, and that $h < M$ if $phi$ is low.
  Let $S'$ be the staircase after the placement and let $T$ be the tile of $p$.
  Then $S'$ is positive, and
  $ T subset.eq U(S), quad U(S') subset.eq U(S), quad U(S) subset.eq T union U(S'), $
  and the interior of $T$ is disjoint from $U(S')$.
] <prop:step>

#proof[
  Write $(a_j, b_j)$, $L_j$ and $M_j$ for the anchors, floors and walls of $S$, and $(a, b)$ for the anchor of $T_i$.
  Since $S$ is positive, the relations $a_(j + 1) = a_j + L_j$ and $b_(j - 1) = b_j + M_j$ give $b_j >= b + M$ for $j < i$, and $a_j >= a + L$ and $b_j + M_j <= b$ for $j > i$, and also $a + L <= W$; moreover $a_(i + 1) = a + L$ and $b_(i + 1) + M_(i + 1) = b$ if $T_i$ is not the last tier, and $a + L = W$ if it is.
  Recall that $w = L$ if $phi$ is not narrow and $h = M$ if $phi$ is not low, so that $w <= L$ and $h <= M$ in every case.

  We first determine the anchors of $S'$.
  The anchor of a tier depends only on the sum of the floors from that tier onwards and on the sum of the walls up to that tier.
  For a tier before $T_i$ the walls up to it are unchanged, and so is the sum of the floors from it onwards: the tiers that replace $T_i$ have floors $w$ and $L - w$, or $L - w$ alone with $w$ added to the floor of $T_(i - 1)$, or $L$, or there are none and $L = w$ is added to the floor of $T_(i - 1)$.
  For a tier after $T_i$ the floors from it onwards are unchanged, and so is the sum of the walls up to it: the tiers that replace $T_i$ have walls $M - h$ and $h$, or $M$, or $M - h$ alone with $h$ added to the wall of $T_(i + 1)$, or there are none and $M = h$ is added to the wall of $T_(i + 1)$.
  Hence every tier of $S$ other than $T_i$ has the same anchor in $S'$, and the same computation gives the anchors of the tiers that replace $T_i$: they are $(a, b + h)$ and $(a + w, b)$ if $phi$ is inside, $(a + w, b)$ if $phi$ is full height, and $(a, b + h)$ if $phi$ is full width.
  The strips of $S'$ are therefore the following.
  The strips of the tiers before $T_i$ are those of $S$, their anchors and walls being unchanged.
  The strip of $T_i$, which is $[a, W] times [b, b + M]$, is replaced by $[a, W] times [b + h, b + M]$ if $phi$ is low, together with $[a + w, W] times [b, b + h]$ if $phi$ is inside, and by $[a + w, W] times [b, b + M]$ if $phi$ is full height.
  The strips of the tiers after $T_i$ are those of $S$, except that the strip $[a + L, W] times [b_(i + 1), b]$ of $T_(i + 1)$ becomes $[a + L, W] times [b_(i + 1), b + h]$ if $phi$ is not narrow.

  The staircase $S'$ is positive: the floor of $T_(i - 1)$ and the wall of $T_(i + 1)$ can only grow, and the new tiers have floors $w$, $L - w$ with $phi$ narrow, or $L$, and walls $M - h$ with $phi$ low, $h$, or $M$.
  The tile $T = [a, a + w] times [b, b + h]$ lies in the strip of $T_i$, because $w <= L$, $a + L <= W$ and $h <= M$.
  Each strip of $S'$ lies in $U(S)$: this is clear for the unchanged ones and for those that replace the strip of $T_i$, which are parts of it, and a point of the enlarged strip of $T_(i + 1)$ lies in the old one if its ordinate is at most $b$, and in the strip of $T_i$ otherwise, since $a + L >= a$ and $h <= M$.
  Let now $(u, v)$ be a point of $U(S)$.
  If it lies in a strip of $S$ other than that of $T_i$, it lies in the corresponding strip of $S'$, which is the same or larger.
  Suppose that it lies in the strip of $T_i$.
  If $phi$ is low and $v >= b + h$, it lies in the strip $[a, W] times [b + h, b + M]$ of $S'$.
  Otherwise $v <= b + h$; if $u <= a + w$ it lies in $T$; if $u > a + w$ and $phi$ is narrow, it lies in the strip of $S'$ with anchor $(a + w, b)$; and if $u > a + w$ and $phi$ is not narrow, then $u > a + L$, so that $T_i$ is not the last tier, and the point lies in the enlarged strip of $T_(i + 1)$.
  This proves that $U(S) subset.eq T union U(S')$.
  Finally let $(u, v)$ be a point of the interior of $T$, so that $a < u < a + w$ and $b < v < b + h$.
  It is in no strip of a tier before $T_i$, since $v < b + M <= b_j$ for $j < i$; in none of the strips that replace that of $T_i$, which require $v >= b + h$ or $u >= a + w$; and in no strip of a tier after $T_i$, which requires $u >= a_j >= a + L >= a + w$.
]

The second part is combinatorial: a floor or a wall that has become non-positive in certain positions can never be removed from the staircase, so that such a staircase cannot be emptied.

#definition(name: [doomed staircase])[
  A real staircase is _floor-doomed_ if it has a tier that is started and whose floor is not positive, or if the floor of its last tier is not positive.
  It is _wall-doomed_ if it has a tier whose wall is not positive and before which every tier is stale.
] <def:doom>

The empty staircase is neither.
The next statement records what the constraints of a single placement give.

#proposition(name: [tile of a placement])[
  Let $x > 0$, and let $p$ be a placement at a tier of a real staircase, with free side $s$, whose positive quantity is positive and whose equation, if it has one, is zero.
  Then the size $(w, h)$ of its tile satisfies $w > 0$ and $h > 0$, and $w = x h$ or $h = x w$.
] <prop:size>

#proof[
  Let $L$ and $M$ be the floor and the wall of the tier.
  For an inside placement $s > 0$ and the size is $(x s, s)$ or $(s, x s)$.
  For a placement of full height $M > 0$ and the size is $(x M, M)$ or $(M slash x, M)$.
  For a placement of full width $L > 0$ and the size is $(L, L slash x)$ or $(L, x L)$.
  For a full placement the size is $(L, M)$ with $L > 0$, and the equation gives $L = x M$, whence $M = L slash x > 0$, or $M = x L > 0$.
]

#proposition(name: [persistence of doom])[
  Let $x > 0$, let $S$ be a real staircase, and let $p$ be a placement that is allowed at $S$, made with a free side for which its positive quantity is positive and its equation, if it has one, is zero.
  Let $S'$ be the staircase after the placement.
  If $S$ is floor-doomed then so is $S'$, and if $S$ is wall-doomed then so is $S'$.
] <prop:doom>

#proof[
  Let $p = (i, phi, o)$, let $L$ and $M$ be the floor and the wall of $T_i$, and let $(w, h)$ be the size of the tile, so that $w, h > 0$ by @prop:size.

  Suppose that $S$ is wall-doomed, and let $T_j$ be a tier whose wall is not positive and before which every tier is stale.
  Since $p$ is allowed, $T_i$ is not stale, so $j <= i$.
  If $j < i$, the wall of $T_j$ is unchanged, and the tiers before $T_j$ remain stale: the placement makes every tier before $T_i$ stale, and clears the flag of $T_(i - 1)$ at most, which is not before $T_j$.
  If $j = i$ then $M <= 0$.
  The fit $phi$ is then low, for otherwise $h = M <= 0$.
  Hence every tier before $T_i$ is stale in $S'$, and the first of the tiers that replace $T_i$ has wall $M - h < 0$.
  In both cases $S'$ is wall-doomed.

  Suppose that $S$ is floor-doomed, and let $T_j$ be a tier whose floor is not positive and which is started or last.
  If $j < i$ then $T_j$ is not last, hence it is started.
  Its floor and its started flag are unchanged by the placement, unless $j = i - 1$ and $phi$ is not low; but that case does not arise, since $p$ is allowed and $T_(i - 1)$ is then not started.
  If $j = i$ then $L <= 0$.
  The fit $phi$ is then narrow, for otherwise the positive quantity of $p$ is $L$.
  Hence the last of the tiers that replace $T_i$ has floor $L - w < 0$ and is started.
  If $j > i$, the floor and the started flag of $T_j$ are unchanged, and $T_j$ is the last tier of $S'$ if it is the last tier of $S$.
  In every case $S'$ is floor-doomed.
]

It follows that doom cannot occur along a record that empties the staircase, and from this that every tile fits.

#proposition(name: [strict fit])[
  Let $x > 0$, let $rho$ be a record that obeys the rules from a real staircase $S$, placed with free sides $s$, and suppose that every positivity constraint of $rho$ on $S$ is positive and every equation is zero.
  Then $S$ is neither floor-doomed nor wall-doomed.
  If moreover $S$ is positive and $rho$ is not empty, then the first placement $p = (i, phi, o)$ of $rho$ has a tile of size $(w, h)$ with $w < L$ if $phi$ is narrow and $h < M$ if $phi$ is low, where $L$ and $M$ are the floor and the wall of $T_i$, and the staircase after $p$ is positive.
] <prop:fit>

#proof[
  The first statement is proved by induction on the length of $rho$.
  If $rho$ is empty then $S$ is empty and is not doomed.
  Otherwise let $S'$ be the staircase after the first placement; the rest of $rho$ obeys the rules from $S'$ and its constraints hold, so $S'$ is not doomed by induction, and neither is $S$ by @prop:doom.

  For the second statement, let $S'$ be the staircase after $p$, which is not doomed by the first statement applied to the rest of $rho$, and recall that $w, h > 0$ by @prop:size.
  If $phi$ is narrow and $w >= L$, then the last of the tiers that replace $T_i$ in $S'$ is started and has floor $L - w <= 0$, so that $S'$ is floor-doomed.
  If $phi$ is low and $h >= M$, then every tier before $T_i$ is stale in $S'$ and the first of the tiers that replace $T_i$ has wall $M - h <= 0$, so that $S'$ is wall-doomed.
  Hence $w < L$ if $phi$ is narrow and $h < M$ if $phi$ is low, and $S'$ is positive by @prop:step.
]

#proposition(name: [soundness])[
  Let $x >= 1$, let $rho$ be a complete admissible record for $n$ tiles, and let $W$, $H$ and $s = (s_1, s_2, dots)$ be real numbers that satisfy the constraints of $rho$ at $x$.
  Then $W > 0$ and $H > 0$, and the tiles of $rho$ for $(x, W, H, s)$ form a similar tiling of $[0, W] times [0, H]$ of proportion $x$ with $n$ tiles.
] <prop:sound>

#proof[
  By @prop:bound the record $rho$ has $n$ placements and obeys the rules from the bare initial staircase, hence from the real initial staircase $S_0$ of $W$ and $H$, since the rules depend on the flags only.
  By @prop:fit the staircase $S_0$ is not doomed.
  Its only tier is the last one and has no tier before it, so its floor $W$ and its wall $H$ are positive, and $S_0$ is positive.

  We show, by induction on the length of a record $rho'$ that obeys the rules from a positive real staircase $S$ and whose constraints on $S$ hold, that the tiles of $rho'$ on $S$ are rectangles of proportion $x$ contained in $U(S)$, that their interiors are pairwise disjoint, that they cover $U(S)$, and that they are as many as the placements of $rho'$.
  If $rho'$ is empty then $S$ is empty and so is $U(S)$.
  Otherwise let $p$ be the first placement of $rho'$, let $T$ be its tile and $S'$ the staircase after it.
  By @prop:size the tile $T$ is a rectangle of proportion $x$, and by @prop:fit it fits its tier strictly where its fit says so and $S'$ is positive, so that @prop:step applies.
  By induction the tiles of the rest of $rho'$ are rectangles of proportion $x$ contained in $U(S')$, with pairwise disjoint interiors, which cover $U(S')$.
  Hence all the tiles are contained in $U(S)$, because $T subset.eq U(S)$ and $U(S') subset.eq U(S)$; the interior of $T$ is disjoint from the later tiles, because it is disjoint from $U(S')$; and the tiles cover $U(S)$, because $U(S) subset.eq T union U(S')$.

  Applied to $rho$ and $S_0$, whose region is $[0, W] times [0, H]$, this shows that the tiles of $rho$ lie in the main rectangle, cover it, and have pairwise disjoint interiors.
  They are $n$ rectangles of proportion $x$, and $x >= 1$.
]

== Completeness <sec:complete>

For completeness, the tiles of a given tiling must be placed in an order for which both rules are obeyed.
The order that places, at each stage, the tile at the first tier at which it fits does not always obey the second rule.
The following notion gives one that does.

#definition(name: [extending floor])[
  Let $R_1, dots, R_n$ be a tiling of $[0, W] times [0, H]$ and let $S$ be a real staircase, read in that rectangle.
  The floor of a tier of $S$, with anchor $(a, b)$ and floor $L$, _extends_ in the tiling if some tile $(a', b', w', h')$ satisfies $b' + h' = b$ and $a' <= a + L < a' + w'$.
] <def:extends>

The floor extends when the segment that carries it continues to the right beyond its end $(a + L, b)$, as the top side of a tile lying below it.
A tile of full height placed at the next tier will then lengthen the floor.
The construction relies on finding the tiles that lie next to a given point.

#proposition(name: [tiles near a point])[
  Let $R_1, dots, R_n$ be a tiling of $[0, W] times [0, H]$, and let $0 <= c < W$.
  If $0 <= d < H$, some tile $(a', b', w', h')$ satisfies $a' <= c < a' + w'$ and $b' <= d < b' + h'$.
  If $0 < d <= H$, some tile $(a', b', w', h')$ satisfies $a' <= c < a' + w'$ and $b' < d <= b' + h'$.
] <prop:near>

#proof[
  Since the tiles are finitely many, there is $epsilon$ with $0 < epsilon < W - c$ such that no tile has the abscissa of its corner in $(c, c + epsilon]$, and there is $eta$ with $0 < eta < H - d$ such that no tile has the ordinate of its corner in $(d, d + eta]$.
  The point $(c + epsilon, d + eta)$ lies in the main rectangle, hence in some tile $(a', b', w', h')$.
  Then $a' <= c + epsilon$, so that $a' <= c$ by the choice of $epsilon$, and $c < c + epsilon <= a' + w'$; likewise $b' <= d < b' + h'$.
  For the second statement, choose $epsilon$ as before and $eta$ with $0 < eta < d$ such that no tile has the ordinate $b' + h'$ of its top side in $[d - eta, d)$.
  The point $(c + epsilon, d - eta)$ lies in some tile $(a', b', w', h')$, for which $a' <= c < a' + w'$ as before, $b' <= d - eta < d$, and $d - eta <= b' + h'$, so that $d <= b' + h'$ by the choice of $eta$.
]

The record is built one placement at a time, and the following conditions are maintained.

#definition(name: [state of the construction])[
  Let $R_1, dots, R_n$ be a tiling of $M = [0, W] times [0, H]$.
  A _state_ consists of a positive real staircase $S$, read in $M$, and of a division of the tiles into _placed_ and _remaining_ ones, such that
  + the interior of every placed tile is disjoint from $U(S)$;
  + the interior of every remaining tile is contained in $U(S)$;
  + $U(S)$ is contained in $M$;
  + the floor of every stale tier of $S$ extends in the tiling, and the floor of no started tier of $S$ does.
] <def:state>

In a state, the tile at each anchor is still to be placed.

#proposition(name: [tile at an anchor])[
  In a state with staircase $S$, for every tier of $S$ there is a remaining tile whose corner is the anchor of the tier.
] <prop:anchor>

#proof[
  Let $(a, b)$, $L$ and $M_i$ be the anchor, the floor and the wall of the tier $T_i$.
  As in the proof of @prop:step, the strips of the earlier tiers lie in the half-plane of ordinates at least $b + M_i$, those of the later tiers in the half-plane of abscissas at least $a + L$, and $a + L <= W$.
  Consequently a point $(u, v)$ with $v < b + M_i$ and $u < a + L$, and with $u < a$ or $v < b$, does not belong to $U(S)$.
  The points $(a, b)$ and $(a, b + M_i)$ belong to the strip of $T_i$, hence to the main rectangle, so that $0 <= a < a + L <= W$ and $0 <= b < b + M_i <= H$.
  By @prop:near some tile $T = (a', b', w', h')$ satisfies $a' <= a < a' + w'$ and $b' <= b < b' + h'$.
  Let $u_0$ be the mean of $a$ and $min(a' + w', a + L)$, and $v_0$ the mean of $b$ and $min(b' + h', b + M_i)$.
  The point $(u_0, v_0)$ lies in the interior of $T$ and in the strip of $T_i$, so $T$ is not placed, and its interior is contained in $U(S)$.
  If $a' < a$, the point with abscissa the mean of $a'$ and $a$ and with ordinate $v_0$ lies in the interior of $T$, but not in $U(S)$ by the remark above; hence $a' = a$.
  If $b' < b$, the point with abscissa $u_0$ and with ordinate the mean of $b'$ and $b$ lies in the interior of $T$, but not in $U(S)$; hence $b' = b$.
]

The placement made in a state is that of the tile at the anchor of the first tier whose floor does not extend.

#proposition(name: [step of the construction])[
  Let $x >= 1$, let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and consider a state whose staircase $S$ is not empty.
  Then some tier of $S$ has a floor that does not extend.
  Let $T_i$ be the first such tier, with floor $L$ and wall $M$, and let $Q = (a, b, w, h)$ be the remaining tile at its anchor.
  Then $w <= L$ and $h <= M$.
  Let $p = (i, phi, o)$, where $phi$ is narrow exactly if $w < L$ and low exactly if $h < M$, and $o$ is wide if $w = x h$ and tall otherwise, and let the free side be $h$ if $o$ is wide and $w$ if $o$ is tall.
  Then $p$ is allowed at $S$, its tile is $Q$, its positive quantity is positive, its equation, if it has one, is zero, and the staircase after $p$, with $Q$ counted as placed, is a state.
] <prop:extension>

#proof[
  The floor of the last tier ends at abscissa $W$, and no tile $(a', b', w', h')$ has $a' <= W < a' + w'$, since the tiles lie in the main rectangle; hence the floor of the last tier does not extend, and $T_i$ exists.
  Recall from the proof of @prop:anchor that $0 <= a < a + L <= W$ and $0 <= b < b + M <= H$.

  Suppose that $w > L$.
  Then $T_i$ is not the last tier, as otherwise $a + L = W$ while $a + w <= W$.
  The anchor of $T_(i + 1)$ is $(a + L, b - M_(i + 1))$ and lies in the main rectangle, so that $b >= M_(i + 1) > 0$.
  By @prop:near, applied to the point $(a + L, b)$, with $0 <= a + L < a + w <= W$ and $0 < b <= H$, some tile $T = (a', b', w', h')$ satisfies $a' <= a + L < a' + w'$ and $b' < b <= b' + h'$.
  If $b < b' + h'$, the interiors of $T$ and $Q$ meet, since the open intervals $(a', a' + w')$ and $(a, a + w)$ both contain the points just to the right of $a + L$, and the open intervals $(b', b' + h')$ and $(b, b + h)$ both contain the points just above $b$; then $T = Q$, which contradicts $b' < b$.
  Hence $b' + h' = b$, and the floor of $T_i$ extends, contrary to the choice of $T_i$.
  This proves that $w <= L$.

  Suppose that $h > M$.
  If $i = 0$ then $b + M = H$, while $b + h <= H$.
  If $i > 0$, the floor of $T_(i - 1)$ extends, by the choice of $T_i$; it ends at the point $(a, b + M)$, so some tile $T = (a', b', w', h')$ satisfies $b' + h' = b + M$ and $a' <= a < a' + w'$.
  The interiors of $T$ and $Q$ meet, since the open intervals $(a', a' + w')$ and $(a, a + w)$ both contain the points just to the right of $a$, and the open intervals $(b', b + M)$ and $(b, b + h)$ both contain the points just below $b + M$; then $T = Q$, which contradicts $b + h > b + M$.
  This proves that $h <= M$.

  The placement $p$ is allowed.
  The tier $T_i$ is not stale, since the floor of a stale tier extends.
  If $phi$ is not low and $i > 0$, the tier $T_(i - 1)$ is not started, since its floor extends and the floor of a started tier does not.

  The tile $Q$ has proportion $x$, so $h = x w$ if $o$ is tall.
  The size of the tile of $p$ is then $(w, h)$, by inspection of the seven cases of @def:placement.
  For an inside placement it is $(x h, h)$ or $(w, x w)$.
  For a placement of full height $h = M$, and the size is $(x M, M) = (x h, h)$ or $(M slash x, M) = (h slash x, h)$.
  For a placement of full width $w = L$, and the size is $(L, L slash x) = (w, w slash x)$ or $(L, x L) = (w, x w)$.
  For a full placement it is $(L, M) = (w, h)$.
  Hence the tile of $p$ is $Q$.
  Its positive quantity is the free side, which is a side of $Q$, or it is $L$ or $M$, and $S$ is positive.
  If $phi$ is full, the equation is $L - x M = w - x h = 0$ if $o$ is wide, and $M - x L = h - x w = 0$ if $o$ is tall.

  Let $S'$ be the staircase after $p$.
  By the choice of $phi$, @prop:step applies: $S'$ is positive, $U(S') subset.eq U(S)$, $U(S) subset.eq Q union U(S')$, and the interior of $Q$ is disjoint from $U(S')$.
  The interiors of the tiles placed before, and that of $Q$, are therefore disjoint from $U(S')$, and $U(S')$ is contained in the main rectangle.
  A remaining tile other than $Q$ has its interior in $U(S)$ and disjoint from that of $Q$, hence disjoint from $Q$ itself, so its interior is contained in $U(S')$.
  It remains to examine the flags of $S'$; recall from the proof of @prop:step that the tiers of $S$ other than $T_i$ keep their anchors.
  The tiers before $T_i$ have floors that extend in $S$.
  Those that are stale in $S'$ have the same floor as in $S$, so their floors extend; none of them is started in $S$, hence none is started in $S'$, where the started flags of these tiers are the same.
  The tiers that replace $T_i$ are not stale, and the only one that is started is the last one in the case of a narrow fit; its anchor is $(a + w, b)$ and its floor is $L - w$, so its floor ends at $(a + L, b)$, as that of $T_i$ does, and does not extend.
  The tiers after $T_i$ have the same anchors, floors and flags as in $S$.
]

#proposition(name: [completeness])[
  Let $x >= 1$, let $W, H > 0$, and let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$.
  Then there are a complete admissible record $rho$ for $n$ tiles and real numbers $s = (s_1, s_2, dots)$ such that $(W, H, s)$ satisfy the constraints of $rho$ at $x$, the tiles of $rho$ for $(x, W, H, s)$ are $R_1, dots, R_n$ in some order, and each placement of $rho$ is wide exactly if its tile $(a, b, w, h)$ satisfies $w = x h$.
] <prop:complete>

#proof[
  The initial staircase of $W$ and $H$, with every tile remaining, is a state: the staircase is positive, its region is the main rectangle, which contains every tile, and its only tier is neither stale nor started.
  We show, by induction on the number $r$ of remaining tiles of a state with staircase $S$, that there are a record $rho'$ of $r$ placements and free sides such that $rho'$ obeys the rules from $S$, its constraints on $S$ hold, its tiles on $S$ are the remaining tiles in some order, and each of its placements is wide exactly if its tile satisfies $w = x h$.
  If $r = 0$ then $S$ is empty, since otherwise there would be a remaining tile by @prop:anchor, and the empty record will do.
  If $r > 0$ then $S$ is not empty, since the interior of a remaining tile is contained in $U(S)$.
  Then @prop:extension gives a placement $p$, with a free side, whose tile is a remaining tile $Q$ and after which there is a state with $r - 1$ remaining tiles, namely those other than $Q$.
  By induction that state has a record $rho''$ with free sides as stated, and $rho'$ is $p$ followed by $rho''$, the free side of $p$, if $p$ is inside, being put before those of $rho''$.
  Applied to the initial state this gives a record $rho$ of $n$ placements that obeys the rules from the initial staircase, which is complete admissible for $n$ tiles by @prop:bound.
]

A square tile is both wide and tall, so that a tiling with square tiles arises from several records; this multiplicity is harmless, since only proportions are counted.
For a square main rectangle, transposition allows the first tile to be taken wide, which halves the number of orientations to be examined.

#proposition(name: [completeness for a square])[
  Let $x >= 1$, let $W > 0$, and let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, W]$ of proportion $x$.
  Then there are a complete admissible record $rho$ for $n$ tiles in which the first tile is wide, and real numbers $s$, such that $(W, W, s)$ satisfy the constraints of $rho$ at $x$ and the tiles of $rho$ are, in some order, either $R_1, dots, R_n$ or their transposes.
] <prop:square>

#proof[
  Let $rho$ and $s$ be given by @prop:complete.
  If $rho$ is empty there is nothing to prove.
  Otherwise its first placement is made at the only tier of the initial staircase, so its tile $T = (0, 0, w, h)$ has its corner at the origin.
  If $w = x h$ the first placement is wide, and $rho$ will do.
  Otherwise $h = x w$, since $T$ has proportion $x$.
  The transposes of $R_1, dots, R_n$ form a similar tiling of the same square, of proportion $x$, as in the proof of @prop:transposition; let $rho'$ and $s'$ be given by @prop:complete for it.
  The tile of the first placement of $rho'$ has its corner at the origin and is the transpose of some $R_j$, whose corner is then the origin; the interiors of $R_j$ and $T$ meet, so $R_j = T$.
  That tile is thus $(0, 0, h, w)$, and $h = x w$ says that the first placement of $rho'$ is wide.
]

== Mosaic classes <sec:mosaic>

The constraints of a record depend only on which tiles border each maximal segment of the tiling, and not on the order in which the corners of tiles on the two sides of a segment alternate.

#definition(name: [mosaic class])[
  A _segment_ of a tiling is a maximal line segment contained in the union of the boundaries of the tiles and not contained in the boundary of the main rectangle, or one of the four sides of the main rectangle.
  Two tilings with $n$ tiles are _mosaic equivalent_ if their tiles can be numbered so that, for each side of each tile, the tiles whose opposite side lies on the same segment are the same in both, and the segments carrying the four sides of the main rectangle correspond.
] <def:mosaic>

Mosaic classes of tilings in which no four tiles meet at a point are the mosaic floorplans of the literature on rectangulations, which are counted by the Baxter numbers $B(n)$ @ackerman2006 @chung1978; the finer classification that also records the alternation of corners along segments gives the generic rectangulations @reading2012.
The staircase construction never distinguishes the order of corners along a vertical segment, and the rule on started floors fixes it along horizontal ones.
Accordingly, for every $n <= 13$ the number of complete admissible records for $n$ tiles, disregarding orientations, is $B(n)$ @oeisA001181.
This agreement is an observation, made by computation.
We have not proved that each mosaic class has exactly one such record, nor that a tiling without a point where four tiles meet arises from only one record; the correctness of the search does not depend on either statement, since a repeated record affects the amount of work and not the set of proportions found.

In terms of electrical networks @bsst1940, each horizontal segment is a node, each tile is a resistor joining the segment that carries its top side to the one that carries its bottom side, the width of a tile is the current through it and its height the potential difference across it.
A wide tile has resistance $1 slash x$ and a tall one resistance $x$.
The equations of a record are Kirchhoff's laws for this network, which is determined by the mosaic class, and for positive resistances these determine the currents.
One therefore expects the equations of every record to have exactly one solution for each $x > 0$, up to scale.
We have not proved this expectation, and the search does not rely on it: it counts the records for which it fails, in the form made precise in @def:regular, and its results are certified only if there are none.

== Solving the system <sec:solving>

For a main rectangle of sides in the ratio $a slash b$, with $a$ and $b$ positive integers, the height is normalised to $H = 1$ and the width $W$ is kept as an unknown, to be compared with $a slash b$ at the end.
Every floor and wall arising along a record is then a linear form in $1$, $W$ and the free sides, whose coefficients are polynomials in the proportion divided by a power of it.

#definition(name: [linear forms])[
  A _linear form_ is a pair $f = (d, c)$ of an integer $d >= 0$ and a sequence $c = (c_0, c_1, c_2, dots)$ of polynomials in $ZZ[x]$; it stands for the expression
  $ (c_0 + c_1 W + c_2 s_1 + c_3 s_2 + dots.c) / x^d. $
  The sum and the difference of $(d, c)$ and $(d', c')$ have exponent $D = max(d, d')$ and coefficients $c_j x^(D - d) plus.minus c'_j x^(D - d')$; the product of $(d, c)$ with $x$ is $(d - 1, c)$ if $d > 0$ and $(0, x c)$ if $d = 0$; and the quotient of $(d, c)$ by $x$ is $(d + 1, c)$.
  With these operations the linear forms are an arithmetic of lengths.
  For an integer $k >= 0$ and real numbers $x != 0$, $W$ and $s_1, dots, s_k$, the _numerator_ and the _value_ of $f$ are
  $ nu_k (f) := c_0 (x) + c_1 (x) W + sum_(j = 1)^k c_(j + 1) (x) s_j, quad "val"_k (f) := nu_k (f) / x^d. $
  The _symbolic system_ of a record $rho$ consists of the positivity constraints and of the equations obtained by placing $rho$ on the initial staircase whose floor is the form $W$ and whose wall is the form $1$, the free sides being the forms $s_1, s_2, dots$.
] <def:forms>

#proposition(name: [symbolic system])[
  Let $rho$ be a record with $k$ inside placements, and let $x != 0$, $W$ and $s = (s_1, s_2, dots)$ be real numbers.
  Then $(W, 1, s)$ satisfy the constraints of $rho$ at $x$ if and only if $"val"_k (f) > 0$ for every positivity constraint $f$ of the symbolic system of $rho$ and $"val"_k (g) = 0$ for every equation $g$ of it.
] <prop:forms>

#proof[
  For $x != 0$ the map $"val"_k$ is a homomorphism from the linear forms to the real numbers: this is a direct verification for each of the four operations, in which numerators are brought to the common power of $x$.
  It sends the form $W$ to $W$, the form $1$ to $1$, and the form $s_j$ to $s_j$ for $j <= k$.
  Since placing commutes with homomorphisms, the positivity constraints and the equations of $rho$ on the real initial staircase of $W$ and $1$, with free sides the values of the forms $s_j$, are the values of those of the symbolic system.
  Only the first $k$ free sides are used, and their values are $s_1, dots, s_k$.
]

The reference form of the search treats each record separately and uses exact arithmetic throughout.
Its arithmetic is performed by three routines, which are not part of what is proved here: the statements below hold for any routines that meet the following specifications.

#definition(name: [exact routines])[
  The _exact routines_ are the following, with their assumed specifications.
  + _Elimination._ Given a square matrix $A$ over $ZZ[x]$, of size $m$, and a vector $c in ZZ[x]^m$, the routine either fails or returns a polynomial $D$ and polynomials $N_1, dots, N_m$.
    In the second case there is $lambda in ZZ[x]$ such that $D = lambda det A$ and $N_i = lambda det A_i$ for every $i$, where $A_i$ is the matrix $A$ with its $i$-th column replaced by $c$.
  + _Roots._ Given a polynomial $q in ZZ[x]$, the routine returns a finite set $"roots"(q)$ of real numbers.
    If $q != 0$, this is the set of the real numbers $r >= 1$ with $q(r) = 0$.
  + _Signs._ Given a real number $r$ and a polynomial $q in ZZ[x]$, the routine returns a sign $"sign"(r, q)$, which is $-1$, $0$ or $1$.
    If $r$ belongs to $"roots"(q')$ for some polynomial $q'$, this is the sign of the real number $q(r)$.
] <def:primitives>

Nothing is assumed of the elimination when it fails.
In the implementation, the elimination is the fraction-free elimination of Bareiss @bareiss1968 with back-substitution, for which $lambda = plus.minus 1$, and it fails when it finds no pivot.
The roots are obtained by factorising $q$ into irreducible factors over $ZZ$ and isolating the real roots of each factor in $[1, infinity)$ by Descartes' rule of signs with bisection @collins1976, so that each root is identified by its minimal polynomial and its position among the roots of that polynomial; factorisation proceeds by reduction modulo a prime exceeding twice the Landau–Mignotte bound on the coefficients of the factors, using Berlekamp's method @berlekamp1970, followed by recombination of the modular factors by trial division.
The sign of $q$ at a root $r$ is zero if and only if the minimal polynomial of $r$ divides $q$, and is otherwise found by evaluating $q$ on an isolating interval for $r$, refined until the value is separated from zero.

#definition(name: [reference method])[
  Let $a$ and $b$ be integers and let $rho$ be a complete admissible record, with $k$ inside placements.
  Let $g_1, dots, g_(k + 1)$ be the equations of its symbolic system, as given by @prop:count, and write $g_r = (d_r, c^((r)))$.
  Let $A$ be the square matrix of size $k + 1$ with entries $A_(r j) := c^((r))_(j + 1)$ for $j <= k$ and $A_(r, k + 1) := c^((r))_1$, and let $c$ be the vector with entries $c_r := -c^((r))_0$, so that the columns of $A$ correspond to the unknowns $s_1, dots, s_k, W$.
  The _reference method_ treats $rho$ as follows.
  + It applies the elimination to $A$ and $c$.
    If the elimination fails, it reports no proportion and counts one _singular situation_.
  + Otherwise, with $D$ and $N_1, dots, N_(k + 1)$ the polynomials returned, it forms $F_rho := b N_(k + 1) - a D$.
    If $F_rho = 0$, it reports no proportion and flags the record as _constant_.
  + Otherwise, if the coefficients of $F_rho (x + 1)$ are all non-negative or all non-positive and its constant coefficient is not zero, it reports no proportion.
  + Otherwise, for each positivity constraint $f = (d, c')$ of the symbolic system it forms $Q_f := c'_0 D + c'_1 N_(k + 1) + sum_(j = 1)^k c'_(j + 1) N_j$.
    It reports the numbers $r in "roots"(F_rho)$ for which $"sign"(r, D) != 0$ and $"sign"(r, Q_f) = "sign"(r, D)$ for every $f$, and it counts one singular situation for each $r in "roots"(F_rho)$ with $"sign"(r, D) = 0$.
  We write $"Ref"_(a, b) (rho)$ for the finite set of numbers reported.
] <def:reference>

On the solutions of the equations, the unknowns are $N_j slash D$ by Cramer's rule, the width is $N_(k + 1) slash D$, and each positivity constraint has numerator $Q_f slash D$; the proportion must be a root of $F_rho$ for the width to be $a slash b$.
The third step is justified by the following test.

#proposition(name: [absence of roots])[
  Let $q in ZZ[x]$ be such that the coefficients of $q(x + 1)$ are all non-negative or all non-positive, and its constant coefficient is not zero.
  Then $q(r) != 0$ for every real number $r >= 1$.
] <prop:noroot>

#proof[
  Let $q(x + 1) = sum_j q_j x^j$, so that $q(r) = q_0 + sum_(j >= 1) q_j (r - 1)^j$ with $r - 1 >= 0$.
  If the $q_j$ are non-negative then $q_0 > 0$ and the sum is non-negative, so $q(r) > 0$; if they are non-positive then $q(r) < 0$ likewise.
]

#proposition(name: [reference method on a record])[
  Let $a$ and $b != 0$ be integers, and let $rho$ be a complete admissible record.
  + Every $r in "Ref"_(a, b) (rho)$ satisfies $r >= 1$, and there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$.
  + If the reference method counts no singular situation for $rho$ and does not flag it as constant, then conversely every real number $r >= 1$ for which there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$ belongs to $"Ref"_(a, b) (rho)$.
] <prop:solve>

#proof[
  Let $k$ be the number of inside placements of $rho$, and keep the notation of @def:reference.
  For a real number $r != 0$ and real numbers $W$ and $s_1, dots, s_k$, write $z := (s_1, dots, s_k, W)$.
  By the definition of $A$ and $c$, the numerator of the equation $g_i$ is $nu_k (g_i) = (A(r) z)_i - c_i (r)$.
  For $r > 0$ a value has the sign of its numerator, so that, by @prop:forms, $(W, 1, s)$ satisfy the constraints of $rho$ at $r$ if and only if $A(r) z = c(r)$ and $nu_k (f) > 0$ for every positivity constraint $f$ of the symbolic system.
  Two facts on the matrix $A$ over the ring $ZZ[x]$ are used, both consequences of the identity between a matrix and its adjugate: $A dot.op (det A_1, dots, det A_(k + 1))^top = (det A) c$, and, for every real vector $z$ with $A(r) z = c(r)$, $(det A)(r) z_i = (det A_i)(r)$ for every $i$.

  For the first statement, let $r in "Ref"_(a, b) (rho)$.
  Then the elimination has succeeded, $F_rho != 0$, and $r in "roots"(F_rho)$, so that $r >= 1$ and $F_rho (r) = 0$, and the signs reported at $r$ are the true signs.
  In particular $D(r) != 0$.
  Let $z_i := N_i (r) slash D(r)$, and let $W := z_(k + 1)$ and $s_j := z_j$.
  Since $D = lambda det A$ and $N_i = lambda det A_i$, the first fact gives $A(r) z = lambda(r) (det A)(r) c(r) slash D(r) = c(r)$.
  From $F_rho (r) = 0$ and $b != 0$ it follows that $W = N_(k + 1) (r) slash D(r) = a slash b$.
  For a positivity constraint $f$, the definition of $Q_f$ gives $Q_f (r) = D(r) nu_k (f)$; since $Q_f (r)$ and $D(r)$ have the same sign, which is not zero, $nu_k (f) > 0$.
  Hence the constraints of $rho$ hold.

  For the second statement, let $r >= 1$ and $s$ be such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$, and let $z := (s_1, dots, s_k, a slash b)$, so that $A(r) z = c(r)$, and $nu_k (f) > 0$ for every positivity constraint $f$.
  The elimination has succeeded, since otherwise a singular situation is counted.
  By the second fact, multiplied by $lambda(r)$, $D(r) z_i = N_i (r)$ for every $i$.
  In particular $F_rho (r) = b N_(k + 1) (r) - a D(r) = D(r) (b dot.op a slash b - a) = 0$.
  The record is not flagged as constant, so $F_rho != 0$; the test of the third step fails, by @prop:noroot; hence the fourth step is reached and $r in "roots"(F_rho)$.
  No singular situation is counted, so $"sign"(r, D) != 0$.
  Finally $Q_f (r) = D(r) nu_k (f)$ with $nu_k (f) > 0$, so $Q_f (r)$ has the sign of $D(r)$, and $r$ is reported.
]

The proviso of the second statement is what the search verifies.

#definition(name: [regular record])[
  Let $a$ and $b$ be integers.
  A complete admissible record is _regular_ for $(a, b)$ if the reference method counts no singular situation for it and does not flag it as constant.
  For an integer $n >= 0$, the reference search _reports_ the numbers of
  $ "Ref"_n (a, b) := union.big_rho "Ref"_(a, b) (rho), $
  where $rho$ ranges over the complete admissible records for $n$ tiles, in which moreover the first tile is wide if $a = b$.
  The reference search for $n$ tiles is _certified_ if all these records are regular for $(a, b)$.
] <def:regular>

A record is thus regular if the elimination succeeds, $F_rho$ is not zero, and $D$ does not vanish at any root of $F_rho$ in $[1, infinity)$, the last condition being void when the test of the third step succeeds.

#proposition(name: [correctness of the reference search])[
  Let $a, b >= 1$ and $n >= 0$ be integers.
  Then $"Ref"_n (a, b) subset.eq P_n (a, b)$.
  If the reference search for $n$ tiles is certified, then $"Ref"_n (a, b) = P_n (a, b)$.
] <prop:reference>

#proof[
  Let $r in "Ref"_(a, b) (rho)$ for a complete admissible record $rho$ for $n$ tiles.
  By @prop:solve, $r >= 1$ and $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$ for some $s$, so by @prop:sound there is a similar tiling of $[0, a slash b] times [0, 1]$ of proportion $r$ with $n$ tiles.
  Hence $r in P_n (a slash b, 1) = P_n (a, b)$, by @prop:scaling.
  Conversely, let $r in P_n (a, b) = P_n (a slash b, 1)$.
  If $a != b$, @prop:complete gives a complete admissible record $rho$ for $n$ tiles and $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$; if $a = b$, @prop:square gives the same with the first tile wide in $rho$.
  If the search is certified, $rho$ is regular, and $r in "Ref"_(a, b) (rho)$ by @prop:solve.
]

By @prop:scaling the set $P_n (a, b)$ is $P_n (a slash b)$.
The implementation counts the singular situations and the records flagged as constant, and both counts were zero in every computation reported in @sec:results; for the computations made with the search of @sec:optimisations, the counts concern the records that it passes to the reference method, which is what @prop:fast requires.
We have not proved that the counts are always zero.
When the search is certified, the set $P_n (a slash b)$ is finite, being the union of the finite sets reported for the finitely many records; this remark is not part of the formal development.

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

We found no closed form, recurrence or generating function for $a(n)$.
The sequence satisfies no linear recurrence with constant coefficients of order at most five, and none with polynomial coefficients of the orders and degrees that thirteen terms allow one to test, a test which does recover the recurrence of the Baxter numbers; the usual transforms of the sequence match no entry of the OEIS, and its residues modulo small integers show no pattern.
The search does, however, reveal a good deal of structure, which we now describe.
@tab:structure collects the counts involved.

#figure(
  kind: table,
  datatable(csv("data/structure.csv")),
  caption: [For $n$ tiles in a square: the number of proportions; the number of those not achievable with fewer tiles; the number achievable by guillotine tilings; the number $E(n)$ of aspect-ratio functions up to inversion; and the number of rational proportions achievable with a single orientation.],
) <tab:structure>

The first phenomenon is that proportions persist.
Cutting one tile into four gives three more tiles, as in @prop:subdivision; cutting it as a square is cut into six squares gives five more; and four more are obtained by surrounding the tiling with a pinwheel.

#proposition(name: [persistence])[
  For all $n >= 2$ and $k >= 3$, $P_n (1) subset.eq P_(n + k) (1)$.
] <prop:persistence>

#proof[
  Every $k >= 3$ is a sum of threes, fours and fives, so it suffices to treat $k in {3, 4, 5}$.
  Replacing a tile of a tiling by a tiling of that tile gives a tiling, and a rectangle of proportion $x$ can be tiled by four rectangles of proportion $x$, and by six: this gives $k = 3$ and $k = 5$.
  For $k = 4$ and $x > 1$, let $p := x slash (x + 1)$.
  Four rectangles with sides $p$ and $p slash x$, placed in the four corners of the unit square in a pinwheel, leave a central square of side $(x - 1) slash (x + 1)$, which is tiled by a scaled copy of the given tiling.
  For $x = 1$, the unit square can be cut into $m$ squares for $m = 4$ and for every $m >= 6$, and $1 in P_n (1)$ with $n >= 2$ requires $n = 4$ or $n >= 6$.
]

@prop:persistence has been formalised in Lean, except for the fact, not needed for the inclusion, that a square cannot be cut into two, three or five squares.
The steps $k = 1$ and $k = 2$ fail: of the $433926$ proportions with ten tiles, only $59264$ recur with eleven.
Consequently almost every proportion is new at the number of tiles at which it first appears, as @tab:structure shows.

The second phenomenon concerns the aspect ratio of the main rectangle as a function of the proportion.
For a tiling with given arrangement and orientations, this is the effective resistance of a planar network whose resistances are $x$ and $1 slash x$ @bsst1940, and it has the following properties.

#proposition(name: [aspect-ratio function])[
  Let $R$ be the aspect-ratio function of an arrangement of $n$ tiles with orientations, in which no tile vanishes identically, and write $R = N slash D$ in lowest terms.
  Then $R$ is odd; $N$ and $D$ have non-negative integer coefficients; one of them is an even polynomial with non-zero constant term and the other is an odd polynomial; their degrees differ by one and are at most $n$, and at most $2 k + 1$ if $k$ tiles have the less frequent orientation; and $R(x) slash x$ is non-increasing and $x R(x)$ non-decreasing on $(0, infinity)$.
] <prop:function>

#proof[
  #todo[the proof, by an energy argument for the network with complex resistances, which locates the roots of $N$ and $D$ on the imaginary axis, is written out in the project notes and is to be brought into an appendix after independent review.]
]

Two consequences follow at once.
The polynomial $N - D$, whose roots in $[1, infinity)$ are the candidate proportions for the square, determines the pair ${R, 1 slash R}$, since $N$ and $D$ are its even and odd parts up to sign.
And its degree has a parity that can be read from the behaviour of $R$.

#proposition(name: [parity of the degree])[
  In the situation of @prop:function, let $d := deg(N - D)$.
  If $R$ tends to $0$ at one end of $(0, infinity)$ and to $infinity$ at the other, then $d$ is odd and $R(x) = 1$ has an odd number of positive solutions, counted with multiplicity.
  Otherwise $d$ and the number of solutions are even.
] <prop:parity>

#proof[
  By @prop:function, $d = max(deg N, deg D)$, the leading coefficient of $N - D$ is positive exactly when $R$ is unbounded at infinity, and $N(0) - D(0)$ is negative exactly when $R$ tends to $0$ at $0$.
  The signs of $N - D$ at the two ends of $(0, infinity)$ therefore differ in the first case and agree in the second, which gives the parity of the number of roots, and the parity of $d$ is that of the odd polynomial among $N$ and $D$ if it has the larger degree, and of the even one otherwise.
]

A function of the first kind always yields a solution, and one of the second kind usually yields none, which accounts for the predominance of odd degrees in @tab:degrees: the proportions of odd degree make up between $82$ and $90$ per cent of all proportions for $7 <= n <= 13$.

The third phenomenon is that the aspect-ratio functions themselves can be counted by the search.
Let $E(n)$ be the number of aspect-ratio functions of arrangements of $n$ tiles with orientations in which no tile vanishes identically, counted up to $R |-> 1 slash R$.

#proposition(name: [wide rectangles])[
  For every $n$ there is $W(n)$ such that $a_w (n) = E(n)$ for every real $w > W(n)$.
  One can take $W(n) = n (1 + 4^n slash 2)$, and one cannot take $W(n) < floor(n^2 slash 4) + 1$.
] <prop:wide>

#proof[
  #todo[the proof is written out in the project notes and is to be brought into an appendix after independent review. Outline: for large $w$ only the functions that are unbounded at infinity can take the value $w$ on $[1, infinity)$, each does so exactly once by the monotonicity in @prop:function, distinct functions do so at distinct points, and no tile vanishes there; a network with non-zero currents is realised by a tiling @bsst1940. The explicit bound uses Kirchhoff's formula for the currents in terms of spanning trees. For the lower bound, the functions $a x + b slash x$ and $a x + x slash b$ with $a + b = n$ take the value $a b + 1$ at the same point $x = b$.]
]

The column of functions in @tab:structure was computed with $w = 1009$, and confirmed with three larger values of $w$ for $n <= 9$ and one for $n = 10$.
For $n <= 10$ it agrees with the counts of distinct functions reported by Einstein @einstein2023, obtained by enumerating networks; the value $E(11) = 9865302$ is new and was computed once.

The fourth phenomenon concerns the rational proportions.
By @tab:rational some of them are achievable with $n$ tiles only if both orientations are used, and from ten tiles onwards the search finds exactly three.

#proposition(name: [exceptional rational proportions])[
  The proportion $n - 4$ belongs to $P_n (1)$ for $n >= 6$, the proportion $n - 11 slash 2$ for $n >= 7$, and the proportion $n - 19 slash 3$ for $n >= 8$.
  None of the three is achievable with $n$ tiles of a single orientation: rectangles of sides $1$ and $n - 4$, $n - 11 slash 2$ or $n - 19 slash 3$ cannot be dissected into $n$ squares.
] <prop:exceptional>

#proof[
  #todo[the proof is written out in the project notes and is to be brought into an appendix after independent review. Outline: the three proportions are the largest rational elements of $P_(n - 4) (1)$ and persist by the pinwheel of @prop:persistence. For the impossibility, in a dissection of a rectangle of height $1$ into squares the number of squares is the integral, over vertical lines, of the sum of the reciprocals of the sides of the squares met; removing the squares of side $1$ reduces the three statements to three finite ones, that a square cannot be cut into five squares, nor a rectangle of sides $3$ and $2$ into seven squares of side less than $2$, nor one of sides $5$ and $3$ into eight squares of side less than $3$.]
]

#conjecture[
  For every $n >= 10$, the rational proportions in $P_n (1)$ that are not achievable with $n$ tiles of a single orientation are exactly $n - 4$, $n - 11 slash 2$ and $n - 19 slash 3$.
] <conj:exceptional>

The conjecture holds for $10 <= n <= 13$; it was formulated from the cases $n = 10$ and $n = 11$ and then confirmed for $12$ and $13$.
For smaller $n$ there are further exceptions, which arise from pinwheels with a central rectangle that is not a square: $5 slash 3$ for six tiles and $16 slash 5$ for nine.
The last column of @tab:structure extends the eight known terms of A210517 @oeisA210517 by five; a sixth, $155656$ for $n = 14$, was also computed.

Finally, the search gives some information on growth.

#proposition(name: [upper bound])[
  For every $n >= 1$, $a(n) <= n 2^(n - 1) M(n)$, where $M(n) = 2 (3 n)! slash ((2 n + 1)! (n + 1)!)$ is the number of rooted non-separable planar maps with $n + 1$ edges.
  In particular $limsup a(n)^(1 slash n) <= 27 slash 2$.
] <prop:upper>

#proof[
  #todo[the proof is written out in the project notes and is to be brought into an appendix after independent review. Outline: the network of a tiling, with an added edge joining its poles, is a non-separable planar map with $n + 1$ edges; there are $2^n$ orientation vectors, of which half need be considered by @prop:transposition, and each function yields at most $n$ proportions, by the bound on the degree in @prop:function.]
]

The quotients $a(n + 1) slash a(n)$ increase throughout the range computed, from $4.80$ at $n = 5$ to $8.68$ at $n = 12$, and the number of proportions achievable by guillotine tilings is a rapidly vanishing share of the total: $90$ per cent for six tiles, and $13.5$ per cent for twelve.
The growth of the guillotine count is bounded by that of the series–parallel networks with two kinds of edge, whose growth constant is about $6.16$.

#conjecture[
  The sequence $a(n + 1) slash a(n)$ is non-decreasing.
] <conj:logconvex>

#conjecture[
  The proportion of the elements of $P_n (1)$ that are achievable by a guillotine tiling with $n$ tiles tends to zero as $n$ tends to infinity.
] <conj:guillotine>

#conjecture[
  For every $n$ and every rational $w > 0$, $a_w (n) <= E(n)$; and $a_w (n) = E(n)$ for every integer $w >= floor(n^2 slash 4) + 2$.
] <conj:threshold>

@conj:logconvex holds for $n <= 12$, and @conj:guillotine is supported by the values for $n <= 12$.
The first part of @conj:threshold holds for $n <= 8$ on the thirty integers and sixteen fractions tried, and we have no argument for it; the second holds for $n <= 8$ and $w <= 30$, and was predicted and then confirmed for $n = 9$.

#todo[add the counts of tilings up to symmetry and of bags of tiles, once computed.]

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

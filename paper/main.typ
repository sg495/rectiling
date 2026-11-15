// SPDX-License-Identifier: LGPL-3.0-or-later
#import "template.typ": appendix, conjecture, definition, example, observation, proof, proposition, template
#import "tables.typ": datatable

#let todo(body) = text(fill: rgb("#b00020"))[[To do: #body]]

#show: template.with(
  title: [Rectangular Dissections into Similar Rectangles],
  authors: ((name: "Stefano Gogioso", affil: "Hashberg Ltd"),),
  abstract: [
    We describe an exact procedure which, for a given $n$ and a main rectangle of rational aspect ratio, finds every proportion $x >= 1$ such that the main rectangle can be cut into $n$ rectangles of proportion $x$, and identifies each as a real algebraic number by its minimal polynomial.
    The procedure places tiles one at a time on a staircase, and solves exactly, for each sequence of placements, a linear system whose coefficients are polynomials in the proportion.
    // We prove that it is sound and complete; the proofs have been formalised in Lean 4, given specifications of the arithmetic routines.
    For the special case of a square, we confirm the known numbers $a(n)$ of proportions for $n <= 10$ and obtain $a(11) = 3446981$, $a(12) = 28799493$ and $a(13) = 250056983$.
    For $n <= 12$ we also count the tilings themselves, their classes under the symmetries of the square, and the multisets of tiles that occur.
    // We prove that a proportion achievable with $n >= 2$ tiles is achievable with $n + k$ tiles for every $k >= 3$, and that $a(n)$ grows at most like $(27 slash 2)^n$.
  ],
)

= Introduction <sec:intro>

A rectangle can be cut into finitely many rectangles that are all similar to one another, each in either orientation; the question is which proportions the pieces can have.
For a square cut into two pieces the only possibility is a pair of halves, of proportion $2$.
For three pieces there are three: thirds, of proportion $3$; a half-height slab above two quarter-size pieces, of proportion $3 slash 2$; and a third arrangement, in which no two pieces are congruent, whose proportion $1.7548...$ is the real root of $x^3 - 2 x^2 + x - 1$, the square of the plastic ratio.

The qualitative question was settled in the 1990s.
Dehn had shown that a rectangle can be cut into squares only if its sides are commensurable @dehn1903, and Brooks, Smith, Stone and Tutte had recast dissections of rectangles as planar electrical networks @bsst1940.
Laczkovich and Szekeres @laczkovich1995, and independently Freiling and Rinne @freiling1994, proved that a square can be cut into rectangles of proportion $x$, for some number of pieces, exactly when $x$ is algebraic and all its conjugates have positive real part; Freiling, Laczkovich and Rinne characterised the rectangles that can be tiled by rectangles similar to a given one, in terms of odd rational functions that map the right half-plane into itself @flr1997, and the electrical point of view was developed further by Prasolov and Skopenkov @prasolov2011.

The quantitative question dates from December 2022, when Baez asked on Mathstodon which proportions are possible when the number $n$ of pieces is fixed @baez2022; a collaborative effort followed, reported in @baez2022 @baez2023 and in the press @roberts2023.
The resulting sequence $a(n)$ is entry A359146 in the OEIS @oeisA359146, which lists $1, 1, 3, 11, 51, 245, 1372$ for $n <= 7$.
The values for $n <= 4$ were found by hand, and those for $5 <= n <= 7$ by exhaustive searches by Henderson @henderson2023 and by Gerbet, reported in @baez2023; Henderson's value for $n = 7$ was corrected after Gerbet's search, and Henderson also reported, tentatively, $a(8) = 8522$.
Taams gave an argument that the proportion is algebraic of degree at most $n$ @taams2023.
Einstein, using the correspondence with electrical networks, reported $a(9) = 58347$ and $a(10) = 433926$ @einstein2023; these two values have not, to our knowledge, been published elsewhere or reproduced.
No formula, recurrence or asymptotic estimate for $a(n)$ is known.

This paper describes an exact search procedure for the problem, for a main rectangle of arbitrary rational aspect ratio, and the results obtained with it.
The procedure builds tilings one tile at a time over a staircase-shaped frontier, turns each combinatorial arrangement into a linear system whose coefficients are polynomials in the proportion, and solves that system exactly, so that every proportion is identified as a real algebraic number by its minimal polynomial.
We reproduce all the values above, by a method independent of both earlier ones, and extend the sequence by three terms:
$ a(11) = 3446981, quad a(12) = 28799493, quad a(13) = 250056983. $

// @sec:tilings fixes definitions.
// @sec:staircases presents the staircases on which tilings are built and the rules that restrict the sequences of placements.
// @sec:systems associates a linear system with each sequence, proves that the construction is sound and complete, and describes the search; the technical part of solving the systems, with the optimisations that make thirteen tiles feasible, is in @app:solving.
// The results are in @sec:results, and further properties of the sets of proportions, with some conjectures, in @app:structure.
// The propositions of @sec:staircases, @sec:systems and @app:solving have been formalised in Lean 4 with Mathlib: the soundness and the completeness of the staircase construction, and the correctness of the direct search and of the incremental search.
// The statements on the two searches take as hypotheses specifications of the exact and of the numerical arithmetic routines, and their completeness is proved under a condition of regularity of the linear systems examined, which the searches verify by counting the exceptions.
// The implementation itself is not verified.
// @app:formal relates the statements of this paper to those of the formal development, and lists what the latter does not cover.

= Tilings <sec:tilings>

We work in the real plane with axis-parallel rectangles.
A rectangle is given by its bottom-left corner and its two side lengths, and its proportion does not depend on which side is the longer.

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

The order of the tiles is immaterial: every rearrangement of a tiling is a tiling.
Two rectangles with disjoint interiors are separated by a horizontal or a vertical line, so that the interior of each is disjoint from the closure of the other; conversely, two tiles of a tiling whose interiors meet are equal.
Both remarks are used repeatedly below.

#definition(name: [achievable proportions])[
  For real numbers $W, H > 0$ and an integer $n >= 0$, let $P_n (W, H)$ be the set of those $x >= 1$ for which the rectangle $[0, W] times [0, H]$ has a similar tiling of proportion $x$ with exactly $n$ tiles.
  We write $P_n (w) := P_n (w, 1)$, $a_w (n) := |P_n (w)|$ and $a(n) := a_1 (n)$.
] <def:counts>

The sets $P_n (w)$ are finite in every case treated in this paper, as a by-product of the computation; see @sec:solving.
A statement labelled Observation is given without proof; its proof is in the formal development (@app:formal).
Scaling the plane preserves proportions, so that only the aspect ratio of the main rectangle matters.

#observation[
  For all $W, H, c > 0$ and $n >= 0$, $P_n (c W, c H) = P_n (W, H)$.
] <prop:scaling>

// #proof[
//   Proportions are invariant under scaling.
//   // Let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and replace each tile $(a, b, w, h)$ by $(c a, c b, c w, c h)$.
//   // The new sides are positive, and $c w = x c h$ if $w = x h$, and likewise with the sides exchanged, so the new tiles have proportion $x$.
//   // A point $p$ lies in a new tile, or in its interior, exactly when $p slash c$ lies in the old one, or in its interior; hence the new tiles cover $[0, c W] times [0, c H]$ exactly and have pairwise disjoint interiors.
//   // This shows that $P_n (W, H) subset.eq P_n (c W, c H)$, and the same statement for the rectangle $[0, c W] times [0, c H]$ and the factor $1 slash c$ gives the other inclusion.
// ]

The _transpose_ of a rectangle $(a, b, w, h)$ is $(b, a, h, w)$.
Transposing every tile turns a tiling of a rectangle into a tiling of the rectangle with the sides exchanged, and wide tiles into tall ones.

#observation[
  For all $W, H > 0$ and $n >= 0$, $P_n (W, H) = P_n (H, W)$.
  Consequently $P_n (w) = P_n (1 slash w)$ for all $w > 0$.
] <prop:transposition>

// #proof[
//   Proportions are invariant under exchange of width/height.
//   // Let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and replace each tile $(a, b, w, h)$ by its _transpose_ $(b, a, h, w)$.
//   // The transpose has positive sides and proportion $x$, the two conditions $w = x h$ and $h = x w$ being exchanged.
//   // A point $(u, v)$ lies in the transpose of a tile, or in its interior, exactly when $(v, u)$ lies in the tile, or in its interior; hence the transposes cover $[0, H] times [0, W]$ exactly and have pairwise disjoint interiors.
//   // This gives $P_n (W, H) subset.eq P_n (H, W)$, and the other inclusion is the same statement with $W$ and $H$ exchanged.
//   // Finally $P_n (w) = P_n (w, 1) = P_n (1, w) = P_n (1 slash w, 1)$, the last equality by @prop:scaling with $c = 1 slash w$.
// ]

The sets of proportions are nested along every step other than one and two, with the exception of the step of four when the main rectangle is not a square.
The step of three was observed by Einstein @einstein2023.

#proposition[
  Let $W, H > 0$ and $n >= 0$.
  + $P_n (W, H) subset.eq P_(n + 3) (W, H)$.
  + If $n >= 2$, then $P_n (1) subset.eq P_(n + 4) (1)$.
  + $P_n (W, H) subset.eq P_(n + k) (W, H)$ for every $k >= 5$.
] <prop:subdivision>

#proof[
  The $P_n (W, H) subset.eq P_(n + 3) (W, H)$ inclusion is shown by subdividing one rectangle into 4 rectangles, all scaled by 1/2.
  The $P_n (1) subset.eq P_(n + 4) (1)$ inclusion is shown by embedding a square tiling as a subdivision of the central tile of a 5-tile pinwheel tiling, where $n >= 2$ is necessary to make the two tilings distinct; as later remarked, this is not true for general rectangles.
  The $P_n (W, H) subset.eq P_(n + k) (W, H)$ inclusion for all $k >=5$ follows from the $k=3$ (shown above), $k=5$ and $k=7$ cases (shown later), by the following observation: every $k >= 5$ can be written as $3a + 5b + 7c$ for non-negative $a, b, c$, because $5 = 2 "mod" 3$ and $7 = 1 "mod" 3$.
  The $P_n (W, H) subset.eq P_(n + 5) (W, H)$ inclusion is shown by subdividing one rectangle into 6 rectangles, one scaled by 2/3 and five scaled by 1/3.
  The $P_n (W, H) subset.eq P_(n + 7) (W, H)$ inclusion is shown by subdividing one rectangle into 8 rectangles, one scaled by 3/4 and seven scaled by 1/4.
  @fig:persistence illustrates all four constructions.
  // Let $R_1, dots, R_n$ be a similar tiling of $M = [0, W] times [0, H]$ of proportion $x$.
  // The corner of $M$ lies in some tile, so $n >= 1$.

  // The unit square can be cut into $m$ squares for $m = 4$ and for every $m >= 6$: into four by its mid-lines; into six, one of side $2 slash 3$ and five of side $1 slash 3$; into eight, one of side $3 slash 4$ and seven of side $1 slash 4$; into seven by cutting one of four squares into four; and cutting one square into four adds three to $m$.
  // Let $R_1 = (a, b, w, h)$.
  // The affine map $(u, v) |-> (a + w u, b + h v)$ sends the unit square onto $R_1$, and sends such a dissection to a tiling $Q_1, dots, Q_m$ of $R_1$ by rectangles whose widths and heights are in the ratio $w slash h$, hence of proportion $x$.
  // The sequence $Q_1, dots, Q_m, R_2, dots, R_n$ is then a tiling of $M$: its union is that of the original tiles, the interiors of the $Q_i$ are pairwise disjoint, and each of them lies in the interior of $R_1$, which is disjoint from the interiors of $R_2, dots, R_n$.
  // It has $n + m - 1$ tiles of proportion $x$.
  // The case $m = 4$ gives the first statement, and the cases $m = k + 1 >= 6$ the second.

  // For the third statement, let $W = H = 1$ and suppose first that $x > 1$.
  // Let $p := x slash (x + 1)$.
  // Four rectangles with sides $p$ and $p slash x$, placed in the four corners of the unit square in a pinwheel, have proportion $x$ and leave a central square of side $(x - 1) slash (x + 1)$, which is tiled by a scaled copy of the given tiling, by @prop:scaling.
  // This gives a similar tiling of the unit square of proportion $x$ with $n + 4$ tiles.
  // If $x = 1$, the hypothesis $n >= 2$ gives $n + 4 >= 6$, and the unit square can be cut into $n + 4$ squares.
]


#figure(
  image("figures/persistence.svg", width: 100%),
  caption: [A similar tiling of the square by five tiles, of proportion $2.7692...$, and the tilings of the same proportion with three, four, five and seven more tiles given by @prop:subdivision: one tile cut into four; a reduced copy of the tiling at the centre of a pinwheel of four tiles, which requires the main rectangle to be a square; one tile cut into six; and one tile cut into eight. The tiles of the original tiling keep their colours, the new tiles are grey, and each tiling is drawn from its record.],
) <fig:persistence>

Steps of $k=1$ and $k=2$ fail to persist in general, and so does the step of $k=4$ for some main rectangles that are not squares.
As counterexamples:

- $2 in P_2 (1)$, while $2 in.not P_3 (1)$ and $2 in.not P_4 (1)$;
- $3 slash 2 in P_1 (3 slash 2)$, while $3 slash 2 in.not P_5 (3 slash 2)$;
- $4 in P_2 (2)$, while $4 in.not P_6 (2)$.

@fig:steps shows the three tilings.
For the square, no proportion with $n=2, 3, 4$ tiles persists at $n=3, 4, 5$ respectively (counterexamples for $k=1$), while five out of the eleven proportions with $n=4$ tiles do not persist at $n=6$ (counterexample for $k=2$); further counts are in @sec:persistence.

#figure(
  image("figures/steps.svg", width: 64%),
  caption: [Tilings whose proportions do not persist, according to the search: the proportion $2$ of the square with $n=2$ tiles, not achievable in the square with $n=3, 4$ tiles (counterexample for $k=1, 2$); the proportion $3 slash 2$ of the rectangle of aspect ratio $3 slash 2$ with $n=1$ tile, not achievable in it with $n=5$ (counterexample for $k=4$); and the proportion $4$ of the rectangle of aspect ratio $2$ with $n=2$ tiles, not achievable in it with $n=6$ (counterexample for $k=4$).],
) <fig:steps>

@fig:three shows every similar tiling of the unit square with three tiles whose bottom-left tile is wide, as found by the search described in @sec:solving; the remaining ones are their transposes.

#figure(
  image("figures/three-tiles.svg", width: 100%),
  caption: [The similar tilings of a square with three tiles in which the bottom-left tile is wide, labelled by proportion. Tiles are coloured in the order in which the search places them.],
) <fig:three>

= Staircases <sec:staircases>

== Staircases <sec:staircase>

The search places tiles one at a time, starting at the bottom-left corner of the main rectangle, in such a way that the region already covered is always closed under moving left and down.
The boundary between the covered and the uncovered region is then a staircase descending from left to right, and the next tile always sits in one of its concave corners.

In the search the lengths of the steps of the staircase are expressions in unknown quantities, and need not take positive values.
The staircase is therefore defined first as a combinatorial object with lengths of an arbitrary kind, and its geometric reading is defined afterwards.

#definition(name: [staircase])[
  An _arithmetic of lengths_ is a set $cal(L)$ with two binary operations, written $ell + ell'$ and $ell - ell'$, and two unary operations, written $x ell$ and $ell slash x$.
  A _tier_ over $cal(L)$ consists of a _floor_ $L in cal(L)$, a _wall_ $M in cal(L)$ and two flags, _stale_ and _started_, each of which is set or clear.
  A _staircase_ over $cal(L)$ is a finite sequence $T_0, dots, T_(m - 1)$ of tiers over $cal(L)$, with $m >= 0$.
  The _initial staircase_ of $W, H in cal(L)$ consists of a single tier with floor $W$, wall $H$ and both flags clear.
  A map $f$ from an arithmetic of lengths to another is a _homomorphism_ if it commutes with the four operations; the _image_ of a staircase under $f$ is obtained by applying $f$ to every floor and wall, keeping the flags.
] <def:staircase>

No law is assumed of these operations, such as associativity or the existence of a neutral element: the statements made for an arbitrary arithmetic of lengths use only the fact that homomorphisms preserve the operations, and two of the arithmetics used below, the linear forms and the intervals, do not satisfy the laws of a module.
Several arithmetics of lengths occur.
The first is the set of real numbers with the usual operations, for a fixed real number $x > 0$; a staircase over it is a _real staircase_.
The second has a single element, so that a staircase over it, a _bare staircase_, is determined by the number of its tiers and their flags; every arithmetic of lengths has exactly one map to it, which is a homomorphism.
The others consist of linear forms in unknown lengths, introduced in @sec:forms and @sec:eager, and of intervals, used in @sec:numeric.

A real staircase is read geometrically inside a main rectangle $[0, W] times [0, H]$: the floors are laid end to end leftwards from the right side, and the walls downwards from the top side.

#definition(name: [anchors and region])[
  Let $S = (T_0, dots, T_(m - 1))$ be a real staircase, with floors $L_i$ and walls $M_i$, and let $W$ and $H$ be real numbers.
  The _anchor_ of the tier $T_i$ is the point $(a_i, b_i)$ with
  $ a_i := W - sum_(j >= i) L_j, quad b_i := H - sum_(j <= i) M_j, $
  its _strip_ is the set of points $(u, v)$ with $a_i <= u <= W$ and $b_i <= v <= b_i + M_i$, and the _region_ $U(S)$ of the staircase is the union of the strips of its tiers.
  The staircase is _positive_ if all its floors and walls are positive.
] <def:region>

By definition $a_(i + 1) = a_i + L_i$ and $b_(i - 1) = b_i + M_i$, with the conventions $a_m := W$ and $b_(-1) := H$: the floor of a tier runs from its anchor to the next anchor, or to the right side of the main rectangle, and its wall runs from its anchor up to the level of the previous anchor, or to the top side.
The region of the initial staircase of $W$ and $H$ is the main rectangle $[0, W] times [0, H]$, and the region of the empty staircase is empty.
@fig:staircase shows a positive staircase with three tiers.
This and the other figures of this section are drawn from tilings found by the search, at their exact proportions.

#figure(
  placement: auto,
  image("figures/staircase.svg", width: 55%),
  caption: [A staircase of proportion $\~1.8695$ after three placements. The anchors $(a_i, b_i)$ are circled; the floor $L_i$ and the wall $M_i$ of the tier $T_i$ are the thick segments that extend to the right and above, respectively, of the anchor. Dashed lines separate the strips of the tiers, which extend to the right side of the main rectangle, and the hatched part of each strip is the rectangle spanned by the floor and the wall, within which a tile placed at the anchor must fit.],
) <fig:staircase>

== Placements <sec:placements>

A tile placed at the anchor of a tier may be at most as wide as the floor and at most as high as the wall, and must be non-empty.
This gives four kinds of placement, each turning a staircase into another.
A tile that is as high as the wall has its height determined by the staircase, and its width by its orientation; a tile that is as wide as the floor is treated symmetrically; a tile that is neither has one free side.

#definition(name: [placement])[
  A _placement_ is a triple $p = (i, phi, o)$ of the index $i >= 0$ of a tier, a _fit_ $phi$, which is _inside_, _full height_, _full width_ or _full_, and an _orientation_ $o$, which is _wide_ or _tall_.
  A fit is _narrow_ if it is inside or full height, and _low_ if it is inside or full width.
  Let $S = (T_0, dots, T_(m - 1))$ be a staircase over $cal(L)$ with $i < m$, let $L$ and $M$ be the floor and the wall of $T_i$, and let $s in cal(L)$, the _free side_.
  The _size_ $(w, h)$ of the tile of $p$ is
  $
    (w, h) := cases(
      (x s, s) & "if" phi "is inside and" o "is wide,",
      (s, x s) & "if" phi "is inside and" o "is tall,",
      (x M, M) & "if" phi "is full height and" o "is wide,",
      (M slash x, M) & "if" phi "is full height and" o "is tall,",
      (L, L slash x) & "if" phi "is full width and" o "is wide,",
      (L, x L) & "if" phi "is full width and" o "is tall,",
      (L, M) & "if" phi "is full.",
    )
  $
  The _positive quantity_ of $p$ is $s$ if $phi$ is inside, $M$ if $phi$ is full height, and $L$ if $phi$ is full width or full.
  If $phi$ is full, the _equation_ of $p$ is the length $L - x M$ if $o$ is wide and $M - x L$ if $o$ is tall; other placements have no equation.
  If $S$ is a real staircase, read in the main rectangle $[0, W] times [0, H]$, the _tile_ of $p$ is the quadruple $(a_i, b_i, w, h)$, where $(a_i, b_i)$ is the anchor of $T_i$.
  By convention, a placement with $i >= m$, at a tier that does not exist, has no size, no positive quantity, no equation and no tile.
] <def:placement>

A placement and a free side determine a tile; placing it changes the staircase as follows.

#definition(name: [placing])[
  Let $S = (T_0, dots, T_(m - 1))$ be a staircase over $cal(L)$, with floors $L_j$ and walls $M_j$, let $p = (i, phi, o)$ be a placement with $i < m$, and let $s in cal(L)$.
  Let $L := L_i$ and $M := M_i$, and let $(w, h)$ be the size of the tile of $p$ on $S$ with free side $s$.
  _Placing_ $p$ on $S$ with free side $s$ gives the staircase $S'$ obtained from $S$ by the following steps.
  + Every tier before $T_i$ becomes stale.
  + If $phi$ is not low and $i > 0$, the floor of $T_(i - 1)$ is replaced by $L_(i - 1) + w$ and its stale flag is cleared.
  + The tier $T_i$ is replaced, according to the fit $phi$.
    + If $phi$ is inside, $T_i$ is replaced by two tiers: the first with floor $w$, wall $M - h$ and both flags clear; the second with floor $L - w$, wall $h$, stale flag clear and started flag set.
    + If $phi$ is full height, $T_i$ is replaced by one tier: floor $L - w$, wall $M$, stale flag clear and started flag set.
    + If $phi$ is full width, $T_i$ is replaced by one tier: floor $L$, wall $M - h$ and both flags clear.
    + If $phi$ is full, $T_i$ is replaced by no tier.
  + If $phi$ is not narrow and $i + 1 < m$, the wall of $T_(i + 1)$ is replaced by $M_(i + 1) + h$.
  The tiers after $T_i$ are otherwise unchanged.
  By convention, placing a placement with $i >= m$ gives $S' := S$, so that placing is defined for every placement; such a placement is never allowed (@def:admissible).
] <def:placing>

@fig:fits shows one placement of each fit, taken from the record of the tiling of @fig:staircase.

#figure(
  image("figures/fits.svg", width: 100%),
  caption: [Four placements in the building of a 7-tile tiling, exemplifying the four kinds of fit. In each panel, the tile just placed is the one sitting in the hatched area, with the floor and wall of its tier before the placement drawn thick.],
) <fig:fits>

Only an inside placement makes use of the free side.
If $phi$ is not narrow then $w = L$, and if $phi$ is not low then $h = M$, by the definition of the size.
In geometric terms, an inside placement replaces the anchor by two, one above the tile and one to its right; a full-height placement moves the anchor to the right and lengthens the floor of the previous tier by $w$; a full-width placement moves the anchor up and heightens the wall of the next tier by $h$; and a full placement removes the anchor, lengthening the floor of the previous tier by $L$ and heightening the wall of the next by $M$.
The number of tiers increases by one with an inside placement, decreases by one with a full placement, and is unchanged otherwise.
Placing commutes with homomorphisms: if $f$ is a homomorphism, the image under $f$ of the staircase obtained by placing $p$ on $S$ with free side $s$ is obtained by placing $p$ on the image of $S$ with free side $f(s)$, and the positive quantity and the equation of $p$ on the image of $S$ are the images of those on $S$.
In particular, the number of tiers and the flags of the staircases obtained by successive placements do not depend on the arithmetic of lengths or on the free sides: they are those of the bare staircases obtained by the same placements.

== Placement rules and records <sec:rules>

A tiling generally admits several orderings in which its tiles can be placed, and tilings that differ only in how the corners of their tiles alternate along a segment impose the same conditions on the sizes of the tiles, as is explained informally in @sec:mosaic.
The search therefore restricts the sequences of placements by two rules, which are expressed by the two flags, and abandons a sequence when fewer tiles remain to be placed than there are tiers.

#definition(name: [allowed and admissible placements])[
  A placement $p = (i, phi, o)$ is _allowed_ at a staircase $S = (T_0, dots, T_(m - 1))$ if the following three conditions hold:

  + $i < m$;
  + the tier $T_i$ is not stale;
  + if $phi$ is not low and $i > 0$, the tier $T_(i - 1)$ is not started.

  A placement $p$ is _admissible_ at $S$ with $r$ tiles remaining if the following three conditions hold:

  + $p$ is allowed at $S$;
  + $r >= 1$;
  + the number $m'$ of tiers after the placement satisfies both:
    + $m' <= r - 1$,
    + $m' = 0$ only if $r = 1$.
] <def:admissible>

#definition(name: [record])[
  A _record_ is a finite sequence $rho = (p_1, dots, p_ell)$ of placements.
  Given a sequence $s_1, s_2, dots$ of free sides, _placing_ $rho$ on a staircase $S$ means placing $p_1, dots, p_ell$ in turn, where the $j$-th inside placement of $rho$ is made with free side $s_j$.
  The record $rho$ _obeys the rules_ from $S$ if each of its placements is allowed at the staircase on which it is placed and the staircase left by the last one is empty.
  The record $rho$ is _admissible for $n$ tiles_ if, on the bare initial staircase, each placement $p_j$ is admissible at the staircase on which it is placed, with $n - j + 1$ tiles remaining.
  An admissible record is _complete_ if, in addition, the staircase left by its last placement is empty.
  The _first tile is wide_ in $rho$ if $rho$ is empty or $p_1$ is wide.
] <def:record>

@fig:rules shows the flags along the record of the tiling of @fig:staircase.
After the first placement, which is inside, the tier $T_1$ to the right of the tile has a started floor.
The third placement is made at $T_1$ and makes $T_0$ stale: no tile can be placed there until its floor is lengthened.
The fourth placement, of full height at $T_1$, lengthens the floor of $T_0$, which ceases to be stale, and it leaves $T_1$ with a started floor, so that a tile of full height or a full tile at $T_2$, which would lengthen that floor, is excluded.
The fifth placement, a full tile at $T_1$, removes that tier, and the tier that was $T_2$ becomes $T_1$, its floor still started.

#figure(
  image("figures/rules.svg", width: 100%),
  caption: [The staircases after one, three, four and five placements of the record of the tiling of @fig:staircase. The anchor of a tier is a circle, or a square if the tier is started, and it is filled grey if the tier is stale.],
) <fig:rules>

Whether a record obeys the rules from a staircase depends only on the flags, hence only on the bare staircase underlying it.
The first rule fixes the order in which tiles at different tiers are placed: a tier becomes stale when a tile is placed at a tier of larger index, and ceases to be stale when its floor is lengthened.
The second concerns a horizontal segment that contains the top sides of some tiles and the bottom sides of others: a floor is started when a tile already stands on its segment to the left, and the rule forbids lengthening such a floor from below, so that the tiles standing on a segment are placed only after all the tiles hanging below it.

A record is thus subject to two conditions, which serve different purposes.
To obey the rules is the condition used in the proofs: soundness and completeness are established in @sec:systems for the records that obey the rules.
To be complete and admissible for $n$ tiles is the condition used by the search: it requires in addition that, after each placement, the staircase has no more tiers than there are tiles still to be placed, and that it becomes empty only with the last tile.
A placement removes at most one tier, so a staircase with more tiers than remaining tiles can no longer be emptied, and the search may abandon such a sequence at once.
The next proposition says that nothing is lost in doing so: for records of $n$ placements the two conditions coincide.

#proposition[
  A record is complete admissible for $n$ tiles if and only if it consists of $n$ placements and obeys the rules from the bare initial staircase.
] <prop:bound>

#proof[
  Let $rho = (p_1, dots, p_n)$ obey the rules from the bare initial staircase, and let $m_j$ be the number of tiers after $p_j$, so that $m_n = 0$.
  A placement removes at most one tier, so $m_j <= n - j$.
  No placement is allowed at the empty staircase, so $m_j > 0$ for $j < n$.
  Since $p_j$ is allowed, these are the conditions of @def:admissible with $n - j + 1$ tiles remaining.

  Conversely, let $rho = (p_1, dots, p_ell)$ be complete admissible for $n$ tiles; it obeys the rules from the bare initial staircase, since an admissible placement is allowed.
  That staircase is not empty, so $ell >= 1$, and $p_ell$ leaves no tier, which @def:admissible permits only with one tile remaining; so $n - ell + 1 = 1$.
]

= Linear systems <sec:systems>

A record of placements imposes a system of linear equations and inequalities on the sizes of the tiles, whose coefficients depend on the proportion.
This section defines the system, proves that its solutions are exactly the similar tilings, and describes how the search uses it.

== The constraints of a record <sec:system>

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
The unknowns are $W$, $H$ and $s_1, dots, s_k$, of which $W$ and $H$ will be given up to a common factor, and a complete record has as many equations as unknowns that remain.

#proposition[
  A record with $k$ inside placements that obeys the rules from a staircase with $m$ tiers has $k + m$ full placements.
  In particular a complete admissible record with $k$ inside placements has $k + 1$ equations.
] <prop:count>

#proof[
  Each placement of the record is made at a tier that exists, so the number of tiers increases by one with each inside placement, decreases by one with each full placement, and is otherwise unchanged.
  It goes from $m$ to zero, so the number of full placements exceeds the number of inside placements by $m$.
  The second statement follows from @prop:bound, since the initial staircase has one tier.
]

#example[
  Consider the record that places a wide tile of full width, then a tall tile of full height, then a wide full tile, all at tier $0$, with $H = 1$.
  The first tile has width $W$ and height $W slash x$, leaving a tier of floor $W$ and wall $1 - W slash x$.
  The second has that wall as its height $h$ and width $h slash x$, and the third has width $W - h slash x$ and height $h$, so the only equation is $W - h slash x - x h = 0$ with $h = 1 - W slash x$, that is,
  $ W = (x^3 + x) / (2 x^2 + 1), $
  and the positivity constraints are $W > 0$, $h > 0$ and $W - h slash x > 0$.
  For $W = 1$ the proportion is the root of $x^3 - 2 x^2 + x - 1$ in $[1, infinity)$, and the tiling is the sixth of @fig:three.
] <ex:plastic>

@fig:example shows the three placements of @ex:plastic.

#figure(
  image("figures/example-steps.svg", width: 100%),
  caption: [The record of @ex:plastic, one placement at a time, at the proportion for which the main rectangle is a square. The sides of each tile are determined by the floor or the wall that it spans.],
) <fig:example>

== Soundness <sec:sound>

The positivity constraints say that tiles have positive size, but not that a tile is narrower than its floor or lower than its wall, although its fit presupposes this.
For records that obey the rules this follows from the rules themselves, so that the rules, which were introduced to avoid repetitions, are also needed for every solution to be a tiling.
The argument has two parts.
The first is geometric (@prop:step): on a positive staircase, if a tile is strictly narrower than its floor when its fit is narrow, and strictly lower than its wall when its fit is low, then placing it removes exactly that tile from the region $U(S)$ of the staircase, the union of the strips of its tiers.
The second is combinatorial (@prop:doom, @prop:fit): along a record that obeys the rules and empties the staircase, these strict inequalities always hold, because a floor or a wall that is not positive in certain positions can never be removed from the staircase.
We begin with the first part.
It rests on the position of the strips of a positive staircase relative to one another.

#observation[
  Let $S$ be a positive real staircase, read in the main rectangle $[0, W] times [0, H]$, and let $T_i$ be a tier of $S$ with anchor $(a, b)$, floor $L$ and wall $M$.
  + The strip of a tier is determined by its anchor and its wall; that of $T_i$ is $[a, W] times [b, b + M]$, and $a + L <= W$ and $b + M <= H$.
  + The strips of the tiers before $T_i$ lie in the half-plane of ordinates at least $b + M$.
  + The strips of the tiers after $T_i$ lie in the half-plane of abscissas at least $a + L$ and in the half-plane of ordinates at most $b$.
  + If $T_i$ is not the last tier, the strip of $T_(i + 1)$ is $[a + L, W] times [b', b]$, where $b'$ is the ordinate of its anchor; if $T_i$ is the last tier, $a + L = W$.
  Consequently a point $(u, v)$ of $U(S)$ with $u < a + L$ and $v < b + M$ lies in the strip of $T_i$, so that $u >= a$ and $v >= b$.
] <obs:strips>

#proposition[
  Let $S$ be a positive real staircase, read in the main rectangle $[0, W] times [0, H]$, and let $p = (i, phi, o)$ be a placement at a tier $T_i$ of $S$, with anchor $(a, b)$, floor $L$ and wall $M$, whose tile $T$ has size $(w, h)$ with $w, h > 0$.
  Suppose that $w < L$ if $phi$ is narrow, and that $h < M$ if $phi$ is low.
  Let $S'$ be the staircase after the placement, and let $U(S)$ and $U(S')$ be the regions of the two staircases according to @def:region.
  + Every tier of $S$ other than $T_i$ has the same anchor in $S'$, and the tiers that replace $T_i$ have the anchors $(a, b + h)$, if $phi$ is low, followed by $(a + w, b)$, if $phi$ is narrow.
  + $S'$ is positive.
  + $T subset.eq U(S)$, $U(S') subset.eq U(S)$ and $U(S) subset.eq T union U(S')$, and the interior of $T$ is disjoint from $U(S')$.
] <prop:step>

#proof[
  A placement changes the region only inside the strip $R := [a, W] times [b, b + M]$ of its own tier: it removes the tile from the bottom-left corner of $R$, and the two parts of $R$ that are left, above the tile and to its right, become the strips of the new tiers or are absorbed by the strip of the next tier.

  _The anchors._
  In @def:placing, what the tiers that replace $T_i$ lack of the floor $L$ is added to the floor of $T_(i - 1)$, and what they lack of the wall $M$ is added to the wall of $T_(i + 1)$.
  The sums of floors and of walls that give the anchors of the other tiers are therefore unchanged, and the tiers that replace $T_i$ are anchored at the corners of the tile that remain on the boundary of the region, as in @fig:fits.
  The floors and walls of $S'$ are those of $S$, possibly increased by $w$ or by $h$, together with $w$, $L - w$ or $L$ and $h$, $M - h$ or $M$ for the new tiers, where $L - w$ occurs only if $phi$ is narrow and $M - h$ only if $phi$ is low; so $S'$ is positive.

  _The region._
  Since $w <= L$ and $h <= M$, the tile $T = [a, a + w] times [b, b + h]$ lies in $R$, hence in $U(S)$, by @obs:strips.
  Let $A := [a, W] times [b + h, b + M]$ and $B := [a + w, W] times [b, b + h]$ be the parts of $R$ above the tile and to its right.
  If $h < M$, then $A$ is the strip of the new tier with anchor $(a, b + h)$.
  If $w < L$, then $B$ is the strip of the new tier with anchor $(a + w, b)$.
  If $w = L$ and $T_i$ is not the last tier, then $B$ lies directly above the strip of $T_(i + 1)$, whose wall the placement increases by $h$, and that strip becomes its union with $B$.
  No other strip changes: the placement otherwise alters only the floor of $T_(i - 1)$ and some flags, on which strips do not depend.
  Hence $U(S')$ is contained in $U(S)$, and it contains the part of $U(S)$ outside the tile, that is, $U(S) subset.eq T union U(S')$.
  The interior of $T$ is disjoint from $A$ and from $B$, and from every other strip by @obs:strips; so it is disjoint from $U(S')$.

  The verification that the tiers of @def:placing have these anchors for each of the four fits, and the cases in which $A$ or $B$ is a segment, are in the formal proof (@app:formal).
]

For the second part, the positions in which a floor or a wall that is not positive can never be removed from the staircase are the following; a staircase with such a floor or wall cannot be emptied.

#definition(name: [defective staircase])[
  A real staircase is _floor-defective_ if it has a tier that is started and whose floor is not positive, or if the floor of its last tier is not positive.
  It is _wall-defective_ if it has a tier whose wall is not positive and before which every tier is stale.
] <def:doom>

The empty staircase is neither.
The next statement records what the constraints of a single placement give.

#proposition[
  Let $x > 0$, and let $p$ be a placement at a tier of a real staircase, with free side $s$, whose positive quantity is positive and whose equation, if it has one, is zero.
  Then the size $(w, h)$ of its tile satisfies $w > 0$ and $h > 0$, and $w = x h$ or $h = x w$.
] <prop:size>

#proof[
  Let $L$ and $M$ be the floor and the wall of the tier.
  If the fit is not full, one side of the tile is the positive quantity of $p$, and the other is that side multiplied or divided by $x$ (@def:placement).
  If the fit is full, the size is $(L, M)$ with $L > 0$, and the equation gives $L = x M$ or $M = x L$, so $M > 0$.
]

A defective staircase stays defective under every allowed placement whose constraints hold, because the floor or the wall that is not positive could be made positive only by a placement that one of the two rules forbids.

#proposition[
  Let $x > 0$, let $S$ be a real staircase, and let $p$ be a placement that is allowed at $S$, made with a free side for which its positive quantity is positive and its equation, if it has one, is zero.
  Let $S'$ be the staircase after the placement.
  + If $S$ is floor-defective, then so is $S'$.
  + If $S$ is wall-defective, then so is $S'$.
] <prop:doom>

#proof[
  Let $p = (i, phi, o)$, let $L$ and $M$ be the floor and the wall of $T_i$, and let $(w, h)$ be the size of the tile, so that $w, h > 0$ by @prop:size.
  Outside $T_i$, the placement makes the tiers before $T_i$ stale; if $phi$ is not low, it lengthens the floor of $T_(i - 1)$ and clears its stale flag; if $phi$ is not narrow, it increases the wall of $T_(i + 1)$; and it changes nothing else (@def:placing).

  _Floors._
  Let $T_j$ be started or last, with a floor that is not positive.
  If $j < i$, then $T_j$ is not last, so it is started, and by the second rule its floor is not lengthened.
  If $j > i$, then $T_j$ keeps its floor and its started flag, and is last in $S'$ if it is last in $S$.
  If $j = i$, then $L <= 0$ is not the positive quantity of $p$, so $phi$ is narrow, and the last tier that replaces $T_i$ is started, with floor $L - w < 0$.

  _Walls._
  Let $T_j$ have a wall that is not positive and only stale tiers before it.
  By the first rule $T_i$ is not stale, so $j <= i$.
  If $j < i$, the wall of $T_j$ is unchanged and the tiers before it stay stale.
  If $j = i$, then $M <= 0 < h$, so $phi$ is low, and the first tier that replaces $T_i$ has wall $M - h < 0$ and only stale tiers before it.

  The identification of the tiers of $S'$ with those of $S$ and those that replace $T_i$, for each of the four fits, is in the formal proof (@app:formal).
]

It follows that no staircase is defective along a record that empties the staircase, and from this that every tile fits.

#proposition[
  Let $x > 0$, let $rho$ be a record that obeys the rules from a real staircase $S$, placed with free sides $s$, and suppose that every positivity constraint of $rho$ on $S$ is positive and every equation is zero.
  + $S$ is neither floor-defective nor wall-defective.
  + Suppose that $S$ is positive and that $rho$ is not empty, let $p = (i, phi, o)$ be the first placement of $rho$, let $L$ and $M$ be the floor and the wall of $T_i$, and let $(w, h)$ be the size of the tile of $p$.
    Then $w < L$ if $phi$ is narrow, $h < M$ if $phi$ is low, and the staircase after $p$ is positive.
] <prop:fit>

#proof[
  For the first statement, a defective staircase stays defective under every placement of $rho$, by @prop:doom, and the staircase left by $rho$ is empty, hence not defective.

  For the second, let $S'$ be the staircase after $p$; it is not defective, by the first statement applied to the rest of $rho$.
  If $phi$ is narrow, the last tier that replaces $T_i$ is started and has floor $L - w$, which is therefore positive.
  If $phi$ is low, the first tier that replaces $T_i$ has wall $M - h$ and only stale tiers before it, so $M - h$ is positive.
  Since $w, h > 0$ by @prop:size, $S'$ is positive by the second statement of @prop:step.

  The induction on the record and the numbering of the free sides in the rest of $rho$ are in the formal proof (@app:formal).
]

Soundness follows by removing the tiles from the region one at a time.

#proposition[
  Let $x >= 1$, let $rho$ be a complete admissible record for $n$ tiles, and let $W$, $H$ and $s = (s_1, s_2, dots)$ be real numbers that satisfy the constraints of $rho$ at $x$.
  Then $W > 0$ and $H > 0$, and the tiles of $rho$ for $(x, W, H, s)$ form a similar tiling of $[0, W] times [0, H]$ of proportion $x$ with $n$ tiles.
] <prop:sound>

#proof[
  By @prop:bound, $rho = (p_1, dots, p_n)$ obeys the rules from the bare initial staircase, hence from the real initial staircase $S_0$ of $W$ and $H$, since the rules depend only on the flags.
  By the first statement of @prop:fit, $S_0$ is not defective; its only tier is last and has no tier before it, so $W > 0$ and $H > 0$, and $S_0$ is positive.

  Let $S_j$ be the staircase after $p_j$, and $Q_j$ the tile of $p_j$, which is a rectangle of proportion $x$ by @prop:size.
  By the second statement of @prop:fit, applied to $(p_j, dots, p_n)$ on $S_(j - 1)$ for $j = 1, dots, n$ in turn, $Q_j$ fits its tier strictly where its fit requires and $S_j$ is positive.
  So @prop:step applies to every placement: $Q_j subset.eq U(S_(j - 1))$, $U(S_j) subset.eq U(S_(j - 1)) subset.eq Q_j union U(S_j)$, and the interior of $Q_j$ is disjoint from $U(S_j)$.

  Since $U(S_0) = [0, W] times [0, H]$ and $U(S_n)$ is empty, the tiles lie in the main rectangle and cover it, and the interior of $Q_j$ is disjoint from every later tile, which lies in $U(S_j)$.

  The formal proof (@app:formal) obtains these properties by one induction on the record, from an arbitrary positive real staircase, and keeps account of the numbering of the free sides.
]

== Completeness <sec:complete>

For completeness, the tiles of a given tiling must be placed in an order for which both rules are obeyed.
The order that places, at each stage, the tile at the first tier at which it fits does not always obey the second rule.
The following notion gives one that does.

#definition(name: [extending floor])[
  Let $R_1, dots, R_n$ be a tiling of $[0, W] times [0, H]$ and let $S$ be a real staircase, read in that rectangle.
  The floor of a tier of $S$, with anchor $(a, b)$ and floor $L$, _extends_ in the tiling if some tile $(a', b', w', h')$ satisfies $b' + h' = b$ and $a' <= a + L < a' + w'$.
] <def:extends>

The floor extends when the segment on which it lies continues to the right beyond its end $(a + L, b)$, as the top side of a tile lying below it.
A tile of full height placed at the next tier will then lengthen the floor.
The construction relies on finding the tiles that lie next to a given point.
For a point $(c, d)$ and a tile $(a', b', w', h')$, the conditions $a' <= c < a' + w'$ and $b' <= d < b' + h'$ hold exactly if the tile contains the points _just above and to the right_ of $(c, d)$, that is, the points $(c + s, d + t)$ for all sufficiently small $s, t > 0$.
The conditions $a' <= c < a' + w'$ and $b' < d <= b' + h'$ hold exactly if it contains the points _just below and to the right_ of $(c, d)$, that is, the points $(c + s, d - t)$ for all sufficiently small $s, t > 0$.

#proposition[
  Let $R_1, dots, R_n$ be a tiling of $[0, W] times [0, H]$, and let $0 <= c < W$.
  + If $0 <= d < H$, some tile $(a', b', w', h')$ satisfies $a' <= c < a' + w'$ and $b' <= d < b' + h'$.
  + If $0 < d <= H$, some tile $(a', b', w', h')$ satisfies $a' <= c < a' + w'$ and $b' < d <= b' + h'$.
] <prop:near>

#proof[
  The tile is one that contains a point above $(c, d)$, or below it, and to its right, so near to $(c, d)$ that no tile has a vertical side whose abscissa, or a horizontal side whose ordinate, lies between those of the two points.
  Since there are finitely many tiles, there are $epsilon$ with $0 < epsilon < W - c$ and $eta$ with $0 < eta < H - d$ such that no tile has a vertical side with abscissa in $(c, c + epsilon]$ or a horizontal side with ordinate in $(d, d + eta]$.
  The point $(c + epsilon, d + eta)$ lies in the main rectangle, hence in some tile $(a', b', w', h')$.
  Then $a' <= c + epsilon$, so that $a' <= c$ by the choice of $epsilon$, and $c < c + epsilon <= a' + w'$; similarly $b' <= d < b' + h'$.
  For the second statement, choose $eta$ with $0 < eta < d$ such that no tile has a horizontal side with ordinate in $[d - eta, d)$, and a tile $(a', b', w', h')$ that contains the point $(c + epsilon, d - eta)$.
  Then $a' <= c < a' + w'$ as before, $b' <= d - eta < d$, and $d - eta <= b' + h'$, so that $d <= b' + h'$ by the choice of $eta$.
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

#proposition[
  In a state with staircase $S$, for every tier of $S$ there is a remaining tile whose corner is the anchor of the tier.
] <prop:anchor>

#proof[
  The tile that contains the points just above and to the right of the anchor has interior points in the strip of the tier, so it is a remaining tile whose interior lies in the region; and the region has no point just to the left of the anchor or just below it, so the corner of the tile is the anchor.

  Let $(a, b)$, $L$ and $M_i$ be the anchor, the floor and the wall of the tier $T_i$.
  The anchor lies in the main rectangle, by the third condition of @def:state, and $a < a + L <= W$ and $b < b + M_i <= H$ by @obs:strips.
  By the first statement of @prop:near, some tile $T = (a', b', w', h')$ satisfies $a' <= a < a' + w'$ and $b' <= b < b' + h'$.
  The set of points $(u, v)$ with $a < u < min(a' + w', a + L)$ and $b < v < min(b' + h', b + M_i)$ is not empty, and it lies in the interior of $T$ and in the strip of $T_i$; so $T$ is not placed, and its interior is contained in $U(S)$.
  If $a' < a$, the points $(u, v)$ with $a' < u < a$ and $v$ as before lie in the interior of $T$, but not in $U(S)$, by the last statement of @obs:strips.
  If $b' < b$, the same holds of the points with $u$ as before and $b' < v < b$.
  Hence $(a', b') = (a, b)$.
]

The placement made in a state is that of the tile at the anchor of the first tier whose floor does not extend.

#proposition[
  Let $x >= 1$, let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$, and consider a state whose staircase $S$ is not empty.
  + Some tier of $S$ has a floor that does not extend.
    Let $T_i$ be the first such tier, with floor $L$ and wall $M$, and let $Q = (a, b, w, h)$ be the remaining tile at its anchor, given by @prop:anchor.
  + The tile $Q$ is at most as wide as the floor and at most as high as the wall: $w <= L$ and $h <= M$.
    Let $p = (i, phi, o)$, where $phi$ is narrow exactly if $w < L$ and low exactly if $h < M$, and $o$ is wide if $w = x h$ and tall otherwise, and let the free side be $h$ if $o$ is wide and $w$ if $o$ is tall.
  + The placement $p$ is allowed at $S$, its tile is $Q$, its positive quantity is positive, and its equation, if it has one, is zero.
  + The staircase after $p$, with $Q$ counted as placed, is a state.
] <prop:extension>

#figure(
  image("figures/construction.svg", width: 100%),
  caption: [The construction of the record of a tiling by six tiles, of proportion $3.4675...$, in the proof of @prop:complete. Before each placement, a floor that extends in the tiling is continued by a dotted segment beyond its right end. The anchors are marked as in @fig:rules: a square for a started tier, filled grey for a stale one. The tile placed next is the one at the anchor of the first tier whose floor does not extend, which is filled black.],
) <fig:construction>

#proof[
  By the choice of $T_i$, its floor does not extend and the floor of every tier before it does.
  The first fact bounds the width of $Q$ and the second its height; with the fourth condition of @def:state, they make $p$ allowed and give that condition after the placement, and @prop:step gives the other three.

  _The tier._
  The floor of the last tier ends at abscissa $W$, by @obs:strips, and no tile $(a', b', w', h')$ has $W < a' + w'$; so this floor does not extend, and $T_i$ exists.

  _The tile fits._
  Suppose that $w > L$.
  The points just above and to the right of the end $(a + L, b)$ of the floor of $T_i$ are then interior points of $Q$.
  By the second statement of @prop:near, some tile $T$ contains the points just below and to the right of this end.
  It is not $Q$, which has no point below the level $b$, so it contains no interior point of $Q$.
  Hence the top side of $T$ is at the level $b$, and the floor of $T_i$ extends, contrary to the choice of $T_i$.

  Suppose that $h > M$.
  Then $i > 0$, since the wall of $T_0$ ends on the top side of the main rectangle, which contains $Q$.
  The floor of $T_(i - 1)$ ends at $(a, b + M)$ and extends: some tile has its top side at the level $b + M$ and contains the points just below and to the right of $(a, b + M)$.
  These are interior points of $Q$, so that tile is $Q$, whose top side is above the level $b + M$.

  _The placement._
  The tier $T_i$ is not stale, since the floor of a stale tier extends, and if $i > 0$ the tier $T_(i - 1)$ is not started, since its floor extends; so $p$ is allowed at $S$.
  By the choice of $phi$ and $o$, $w = L$ if $phi$ is not narrow, $h = M$ if $phi$ is not low, and $w = x h$ or $h = x w$ according as $o$ is wide or tall.
  With the free side chosen, the size given by @def:placement is therefore $(w, h)$, so the tile of $p$ is $Q$; its positive quantity is a side of $Q$; and its equation, if $phi$ is full, is $w - x h$ or $h - x w$, which is zero.

  _The new state._
  Let $S'$ be the staircase after $p$.
  By the choice of $phi$, @prop:step applies to $p$: $S'$ is positive, and $U(S')$ is contained in $U(S)$, is disjoint from the interior of $Q$, and contains the part of $U(S)$ outside $Q$.
  The first three conditions of @def:state follow, since the interior of a remaining tile other than $Q$ is disjoint from $Q$.

  Whether a floor extends depends only on the point at which it ends.
  A tier of $S$ other than $T_i$ keeps its anchor, by the first statement of @prop:step, its started flag, and its floor, unless it is $T_(i - 1)$ and its floor is lengthened, in which case it is not stale in $S'$.
  The tiers before $T_i$ have floors that extend in $S$ and are not started, and the tiers after $T_i$ also keep their stale flags; so the fourth condition holds in $S'$ for all of them.
  Of the tiers that replace $T_i$ none is stale, and the only one that is started is the one to the right of $Q$, if $phi$ is narrow; its floor ends at $(a + L, b)$, as that of $T_i$ does, and so does not extend.

  Two verifications are left to the formal proof (@app:formal): that $b > 0$ when $w > L$, which @prop:near requires and which holds because $T_i$ is then not the last tier, and the size in each of the seven cases of @def:placement.
]

Repeating the step until no tile remains gives the record.

#proposition[
  Let $x >= 1$, let $W, H > 0$, and let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, H]$ of proportion $x$.
  Then there exist a complete admissible record $rho$ for $n$ tiles and real numbers $s = (s_1, s_2, dots)$ such that $(W, H, s)$ satisfy the constraints of $rho$ at $x$, the tiles of $rho$ for $(x, W, H, s)$ are $R_1, dots, R_n$ in some order, and each placement of $rho$ is wide exactly if its tile $(a, b, w, h)$ satisfies $w = x h$.
] <prop:complete>

#proof[
  The initial staircase of $W$ and $H$, with every tile remaining, is a state: the staircase is positive, its region is the main rectangle, which contains every tile, and its only tier is neither stale nor started.
  We show, by induction on the number $r$ of remaining tiles of a state with staircase $S$, that there exist a record $rho'$ of $r$ placements and free sides such that $rho'$ obeys the rules from $S$, its constraints on $S$ hold, its tiles on $S$ are the remaining tiles in some order, and each of its placements is wide exactly if its tile satisfies $w = x h$.
  If $r = 0$ then $S$ is empty, since otherwise there would be a remaining tile by @prop:anchor, and the empty record suffices.
  If $r > 0$ then $S$ is not empty, since the interior of a remaining tile is contained in $U(S)$.
  Then @prop:extension gives a placement $p$, with a free side, whose tile is a remaining tile $Q$ and after which there is a state with $r - 1$ remaining tiles, namely those other than $Q$.
  By induction that state has a record $rho''$ with free sides as stated, and $rho'$ is $p$ followed by $rho''$; the free side of $p$, if $p$ is inside, precedes those of $rho''$.
  Applied to the initial state this gives a record $rho$ of $n$ placements that obeys the rules from the initial staircase of $W$ and $H$, hence from the bare initial staircase, since the rules depend only on the flags; so $rho$ is complete admissible for $n$ tiles by @prop:bound.
]

A square tile is both wide and tall, so that a tiling with square tiles arises from several records; this does not affect the count of proportions.
For a square main rectangle, transposition allows the first tile to be taken to be wide, which halves the number of orientations to be examined.

#proposition[
  Let $x >= 1$, let $W > 0$, and let $R_1, dots, R_n$ be a similar tiling of $[0, W] times [0, W]$ of proportion $x$.
  Then there exist a complete admissible record $rho$ for $n$ tiles in which the first tile is wide, and real numbers $s$, such that $(W, W, s)$ satisfy the constraints of $rho$ at $x$ and the tiles of $rho$ are, in some order, either $R_1, dots, R_n$ or their transposes.
] <prop:square>

#proof[
  Let $rho$ and $s$ be given by @prop:complete.
  If $rho$ is empty there is nothing to prove.
  Otherwise its first placement is made at the only tier of the initial staircase, so its tile $T = (0, 0, w, h)$ has its corner at the origin.
  If $w = x h$ the first placement is wide, and $rho$ suffices.
  Otherwise $h = x w$, since $T$ has proportion $x$.
  The transposes of $R_1, dots, R_n$ form a similar tiling of the same square, of proportion $x$, as in @prop:transposition; let $rho'$ and $s'$ be given by @prop:complete for it.
  The tile of the first placement of $rho'$ has its corner at the origin and is the transpose of some $R_j$, whose corner is then the origin; the interiors of $R_j$ and $T$ meet, so $R_j = T$.
  That tile is thus $(0, 0, h, w)$, and $h = x w$ means that the first placement of $rho'$ is wide.
]

== The search <sec:solving>

By @prop:sound and @prop:complete, the proportions achievable with $n$ tiles in a main rectangle of sides $a slash b$ and $1$ are the numbers $x >= 1$ at which the constraints of some complete admissible record for $n$ tiles have a solution with $W = a slash b$ and $H = 1$; for a square, by @prop:square, only the records in which the first tile is wide need be considered.
The search examines these records, of which there are finitely many, and determines the proportions of each exactly.

Let $rho$ be a complete admissible record with $k$ inside placements, and take $H = 1$.
Every floor and wall that arises along $rho$ is a linear form in $1$, $W$ and the free sides $s_1, dots, s_k$, whose coefficients are polynomials in $x$ divided by a power of $x$, and by @prop:count the record has $k + 1$ equations in the $k + 1$ unknowns $s_1, dots, s_k$ and $W$.
Clearing the powers of $x$ gives a square matrix $A$ and a vector $c$ over $ZZ[x]$, and by Cramer's rule, at every $x$ at which $D := det A$ does not vanish, the system has exactly one solution, whose width is $N(x) slash D(x)$ for a polynomial $N$; in @ex:plastic, $N slash D = (x^3 + x) slash (2 x^2 + 1)$.
The proportion must therefore be a root of the _proportion polynomial_
$ F_rho := b N - a D $
of the record, and a root $r >= 1$ of $F_rho$ is the proportion of a tiling with the record $rho$ exactly if every positivity constraint is positive at the solution for $x = r$.
The search isolates the real roots of $F_rho$ in $[1, infinity)$, identifying each by its minimal polynomial, and determines the signs of the positivity constraints at each of them.
The record is _regular_ if $D$ is not zero, $F_rho$ is not zero, and $D$ does not vanish at any root of $F_rho$ in $[1, infinity)$; the precise form of this condition is @def:regular.
At a root of $F_rho$ where $D$ vanishes the system might have further solutions, which the search would not find, so that the search counts the records that are not regular, and its result is _certified_ if there are none.

The search exists in two forms, which are defined and proved correct in @app:solving.
The _direct search_ treats each record on its own, by a fraction-free elimination over $ZZ[x]$ followed by exact determinations of signs at the roots (@def:reference).
The _incremental search_, which is the one used for the results of @sec:results, explores the records depth first, as paths in the tree of admissible sequences of placements, and uses each equation as soon as its full placement is made to eliminate one unknown from every floor and wall of the current staircase (@def:explore).
The work done for a sequence of placements is thus shared by all the records that begin with it, and most of the nodes of the tree are close to its leaves, where staircases have one or two tiers.
The incremental search decides the signs at a root by interval arithmetic with outward rounding, and passes a record that it cannot decide in this way to the direct method, which for ten tiles occurs for one record in ten thousand.
Its cost is about $0.6$ microseconds of processor time per record.

#proposition[
  Let $a, b >= 1$ and $n >= 0$ be integers.
  Every number reported by the direct search or by the incremental search for $n$ tiles and the main rectangle of sides $a$ and $b$ belongs to $P_n (a slash b)$.
  If the search is certified, the numbers that it reports are exactly the elements of $P_n (a slash b)$.
] <prop:search>

#proof[
  For the direct search this is @prop:reference, with the notion of a certified search of @def:regular, and for the incremental search it is @prop:fast, with that of @def:fastcert.
  Both are proved in @app:solving from @prop:sound, @prop:complete and @prop:square, under the specifications of the arithmetic routines that are stated there.
]

By @prop:scaling the set $P_n (a, b)$ is $P_n (a slash b)$.
The implementation counts the singular situations and the records flagged as constant, and both counts were zero in every computation reported in @sec:results; for the computations made with the incremental search, the counts concern the records that it passes to the direct method, which is what @prop:fast requires.
We have not proved that the counts are always zero.
When the search is certified, the set $P_n (a slash b)$ is finite, since it is the union of the finite sets reported for the finitely many records; this remark is not part of the formal development.


Three features of the problem make the incremental search efficient.
First, records share their beginnings, and the elimination made for a beginning serves every record that continues it.
Secondly, different records often lead to the same polynomial: for a square and thirteen tiles, $2.8 times 10^11$ records lead to $2.6 times 10^8$ polynomials with a root in $[1, infinity)$, each of which is factorised once.
Thirdly, when the sign of a positivity constraint at a root cannot be decided numerically, it is almost always because the constraint is exactly zero there: the solution is then a tiling with fewer tiles, one tile of the record having degenerated, as in @fig:pinwheel.
About one root in a hundred is of this kind, and an exact test of divisibility by the minimal polynomial of the root decides these cases without recourse to the direct method (@def:check).

#figure(
  image("figures/pinwheel.svg", width: 100%),
  caption: [The pinwheel arrangement of five tiles, with four wide tiles and one tall: the exact solution of the system of its record, with the width of the main rectangle left free, for three values of the proportion. The central tile has height $(x^2 - 1) slash (5 x^2 + 3)$, and the width of the main rectangle is $x (3 x^2 + 5) slash (5 x^2 + 3)$. The main rectangle is a square only for $x = 1$, where the central tile has size zero: the candidate root is rejected, and what remains is a tiling by four squares.],
) <fig:pinwheel>

The smallest case in which the search has anything to decide is that of two tiles.

#example[
  Let $a = b = 1$ and $n = 2$.
  A first placement that is inside would leave two tiers for one tile, and a full one would leave none for one tile, so the admissible first placements are of full width or of full height, and wide, since the main rectangle is a square; the second placement is full, of either orientation.
  There are thus four complete admissible records, shown in @tab:two.
  After a wide tile of full width, of height $1 slash x$, the only tier has floor $1$ and wall $1 - 1 slash x$; a wide full tile requires $1 = x (1 - 1 slash x)$, that is $x = 2$, and a tall one requires $1 - 1 slash x = x$, which has no real solution.
  After a wide tile of full height, of width $x$, the only tier has floor $1 - x$ and wall $1$, and the two equations are $1 - x = x$ and $1 = x (1 - x)$, neither of which has a solution in $[1, infinity)$; indeed the floor $1 - x$ is not positive for $x >= 1$.
  The search therefore reports the single proportion $2$, and $a(2) = 1$.
] <ex:two>

#figure(
  kind: table,
  table(
    columns: 4,
    align: (left, left, left, left),
    table.header([first placement], [second placement], [proportion polynomial], [roots in $[1, infinity)$]),
    table.hline(stroke: 0.05em),
    [full width, wide], [full, wide], [$x - 2$], [$2$],
    [full width, wide], [full, tall], [$x^2 - x + 1$], [none],
    [full height, wide], [full, wide], [$2 x - 1$], [none],
    [full height, wide], [full, tall], [$x^2 - x + 1$], [none],
  ),
  caption: [The four records examined for two tiles in a square.],
) <tab:two>

#figure(
  image("figures/two-tiles.svg", width: 44%),
  caption: [The two placements of the only record that yields a tiling of the square by two tiles, at its proportion $2$.],
) <fig:two>

= Results <sec:results>

All computations were carried out with the Rust implementation of the search, on an M4 Max 128 GB machine.
All runs used the incremental search, except where stated.
In every run the implementation's counters for singular systems, for aspect ratios independent of the proportion, and for coefficients exceeding machine integers within the direct method were all zero.
In the incremental search these counters concern the records passed to the direct method, so that every unrestricted run of the incremental search was certified in the sense of @def:fastcert, which is the hypothesis under which @prop:fast identifies the numbers found with the achievable proportions; the runs of the direct search, used for comparison, were certified in the sense of @def:regular, as @prop:reference requires.
The computations restricted to guillotine tilings or to tilings with few tiles in one orientation, used in @app:structure, are made by variants of the search that @sec:systems and @app:solving do not cover.

== The square <sec:square>

@tab:counts lists $a(n)$ for $n <= 13$, with the number of records examined, which is $2^(n - 1) B(n)$ in each case, where $B(n)$ is the $n$-th Baxter number (@sec:mosaic), the number of pairs of a record and a proportion that it realises, which we call _realisations_, and the number of distinct polynomials with a root in $[1, infinity)$ that the search encountered.
The last number depends on the search method and is not an invariant of the problem.

#figure(
  kind: table,
  datatable(csv("data/counts.csv")),
  caption: [Proportions for the square. A record is an admissible sequence with orientations in which the first tile is wide; a realisation is a record with a proportion that it realises. The last column is the time of the run, in seconds.],
) <tab:counts>

The values for $n <= 7$ agree with those of Henderson and Gerbet, the value for $n = 8$ agrees with Henderson's, and the values for $n = 9$ and $n = 10$ agree with those reported by Einstein.
The values for $n = 11$, $12$ and $13$ are new.
Those for $n = 11$ and $n = 12$ were each computed twice, with the direct treatment of degenerate tiles and with the certificate of @def:check, with identical results; the value for $n = 13$ was computed once and took three hours.

The search was checked in several further ways.
For $n <= 9$ the incremental search and the direct search agree on every proportion and on the number of records realising it.
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

Odd degrees are more frequent than the neighbouring even ones; a heuristic reason is given after @prop:parity-full.
Degree $n$ is attained for every $n$ in the table other than $4$.

The proportions of degree one are explained in part by dissections into squares.
If all tiles of a similar tiling of the square have the same orientation, stretching one axis by the proportion gives a dissection of a rectangle into $n$ squares, whose aspect ratio is the proportion.
The number of aspect ratios of rectangles that can be dissected into $n$ squares is entry A210517 in the OEIS @oeisA210517, which lists $1, 1, 2, 5, 11, 28, 74, 211$.
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

== Growth <sec:growth>

We found no closed form, recurrence or generating function for $a(n)$.
The sequence satisfies no linear recurrence with constant coefficients of order at most five, and none with polynomial coefficients of the orders and degrees that thirteen terms allow one to test, a test which recovers the recurrence of the Baxter numbers; the usual transforms of the sequence match no entry of the OEIS, and its residues modulo small integers show no pattern.
The sets of proportions have some structure: proportions persist when tiles are added, the aspect ratio of the main rectangle is a rational function of the proportion of a restricted kind, these functions are counted by the proportions for wide main rectangles, and all but three of the rational proportions for ten or more tiles are explained by dissections into squares.
These properties, and the conjectures that the computations suggest, are the subject of @app:structure.
Here we bound the growth of $a(n)$.

The bound rests on the electrical network of a tiling @bsst1940, whose vertices are the horizontal lines of the tiling, whose poles $s$ and $t$ are the top and bottom sides of the main rectangle, and whose edges are the tiles; the current in a tile is its width and the potential difference across it is its height (@def:tiling-network).
The network $frak(N)(tau)$ of a tiling $tau$ is drawn in the plane with both poles on the outer face, and $G^+$ denotes its graph with an additional edge $e_0$ joining the poles (@def:plane-network).
For an orientation vector $epsilon$, which labels each edge as tall or wide, the impedance $Z_(frak(N), epsilon)$ of a network $frak(N)$ between its poles, when every tall edge has resistance $x$ and every wide edge resistance $1 slash x$, is a rational function of $x$ (@def:impedance).
A similar tiling $tau$ of $[0, W] times [0, H]$ of proportion $x$, with orientations $epsilon$, satisfies $H slash W = Z_(frak(N)(tau), epsilon) (x)$, by @prop:tiling-network.

A _planar map_ is a connected graph, possibly with multiple edges, embedded in the sphere, and considered up to the homeomorphisms of the sphere.
It is _non-separable_ if it has no loop and no vertex whose removal disconnects it; the map with two vertices and two parallel edges is included.
A map is _rooted_ by the choice of an edge, of a direction of that edge and of one of its sides.
The following result of Tutte @tutte1963 is used without proof: the number of rooted non-separable planar maps with $m >= 2$ edges is $2 (3 m - 3)! slash (m! thin (2 m - 1)!)$.
For $m = n + 1$ this is
$ M(n) := (2 (3 n)!) / ((2 n + 1)! thin (n + 1)!). $

#proposition[
  The number of proportions for the square satisfies
  $ limsup_(n -> infinity) a(n)^(1 slash n) <= 27 / 2. $
  More precisely, $a(n) <= n 2^(n - 1) M(n)$ for every $n >= 1$.
] <prop:upper>

#proof[
  Let $x in P_n (1)$, and let $tau$ be a similar tiling of the unit square of proportion $x$ with $n$ tiles.
  Transposing if necessary, by @prop:transposition, the tile at the bottom-left corner is wide; let $epsilon$ be an orientation vector of $tau$ for which that tile has orientation $-1$; if $x = 1$, all orientations are taken to be $-1$.
  Root the map $G^+$ of $frak(N)(tau)$ at $e_0$; the edge of the bottom-left tile is then the first edge after $e_0$ in the rotation at $t$, on a side fixed once and for all.
  By @prop:tiling-network, $Z_(frak(N)(tau), epsilon) (x) = 1$, so that $x$ is a root of $N - D$, where $N slash D$ is this function in lowest terms.
  By @prop:reactance, $N - D$ is not zero and has degree at most $n$, and it depends only on the isomorphism class of the rooted map with its orientation vector.
  By @prop:nonseparable and the result of Tutte there are at most $M(n)$ rooted maps, each with at most $2^(n - 1)$ orientation vectors in which the distinguished edge has orientation $-1$, and each pair contributes at most $n$ roots.
  This gives the bound on $a(n)$, and the limit follows by Stirling's formula, by which $M(n)$ is asymptotic to a constant times $(27 slash 4)^n n^(-5 slash 2)$.
]


The same bound for the number of realisations of @tab:counts is proved only under three combinatorial hypotheses, which are stated in @sec:mosaic.
The quotients $a(n + 1) slash a(n)$ increase throughout the range computed, from $4.80$ at $n = 5$ to $8.68$ at $n = 12$.

#conjecture[
  The sequence $a(n + 1) slash a(n)$ is non-decreasing.
] <conj:logconvex>

@conj:logconvex holds for $n <= 12$.
The rate $27 slash 2$ is not attained: @prop:deficit shows that $limsup t(n)^(1 slash n)$, and hence $limsup a(n)^(1 slash n)$, is smaller than $27 slash 2$, by an amount too small to be detected in the values computed.
Whether $a(n)^(1 slash n)$ converges is not known (@sec:growth-rate).

== Tilings, classes and bags <sec:tilings-counts>

The numbers $a(n)$ count proportions, and each proportion is in general realised by many tilings.
We now count the tilings themselves, in three ways.

#definition(name: [tilings, classes and bags])[
  For $n >= 1$, let $t(n)$ be the number of similar tilings of the unit square with $n$ tiles, where a tiling is regarded as a set of rectangles.
  Let $b(n)$ be the number of orbits of these tilings under the group of the eight symmetries of the square.
  The _bag_ of a similar tiling of proportion $x$ is the pair of $x$ and the multiset of the short sides of its tiles, and $c(n)$ is the number of bags of similar tilings of the unit square with $n$ tiles.
] <def:tbc>

Two tilings have the same bag exactly when the tiles of one can be rearranged, with rotations by a quarter turn allowed, into the other.
The number $t(n)$ is finite.
Indeed there are finitely many proportions, by @prop:upper, and finitely many records, and a record has at most one solution at a given proportion: since the constraints are linear equations and strict linear inequalities in the free sides, two solutions would be joined by a segment of solutions, which give infinitely many tilings with the same record; two of these would have the same network, with the same edge for each placement, hence the same flow by @prop:flow and the same tiles.
A tiling determines its bag, and symmetric tilings have the same bag, so that
$ a(n) <= c(n) <= b(n) <= t(n) <= 8 b(n). $
The sequence $b(n)$ is the one requested in the entry A359146 @oeisA359146, which records $b(1) = 1$, $b(2) = 1$, $b(3) = 3$ and $b(4) > 11$.
@tab:tbc gives the values that we computed, @fig:sequences plots the four sequences, and @fig:classes shows the sixteen classes for four tiles.

#figure(
  kind: table,
  datatable(csv("data/tilings-counts.csv")),
  caption: [Bags, classes under symmetry and tilings for the unit square, with the number of proportions for comparison.],
) <tab:tbc>

#figure(
  image("figures/sequences.svg", width: 62%),
  caption: [The numbers of tilings, classes, bags and proportions for the square, on a logarithmic scale. The numbers of bags $c(n)$ and of proportions $a(n)$ differ by less than six per cent throughout, and their curves nearly coincide. The dashed curves are fits to the terms computed: $0.295 dot.op 2^n M(n)$ and one eighth of it, in the colours of the tilings and of the classes, and $0.676 dot.op (27 slash 2)^n n^(-11 slash 2)$, in the colour of the proportions. They are not asymptotic forms, since the rate of growth is smaller than $27 slash 2$ by @prop:deficit.],
) <fig:sequences>

#figure(
  image("figures/classes-4.svg", width: 100%),
  caption: [One tiling from each of the $16$ classes of tilings of the square by four similar rectangles, labelled by proportion, with the number of tilings of the class in brackets; the numbers add up to $t(4) = 89$.],
) <fig:classes>

The search described in @sec:solving counts records, not tilings, and the passage from one to the other requires three corrections, each made exactly.
A tiling of proportion $x > 1$ has one orientation vector, and the search examines it or its transpose, which is a different tiling since transposition exchanges the orientations; a tiling by squares has $2^n$ orientation vectors.
A tiling in which four tiles meet at a point arises from several records, as the following proposition makes precise; we call such a point a _crossing_.
A tiling is identified by its proportion, its orientations and the record described in @prop:representative, since the solution of a reported record at a proportion is unique.
The order of the coordinates of the sides of its tiles, which determines that record, the crossings and the symmetries, is computed exactly: the coordinates are elements of the number field of the proportion, floating-point enclosures are used only to certify strict inequalities, and equalities are decided by divisibility by the minimal polynomial.
Both this and the count of bags assume that the polynomial stored for a proportion is its minimal polynomial, which the search for proportions does not need.

#proposition[
  Let $cal(T)$ be a similar tiling, with a choice of orientation for each tile.
  A complete admissible record _yields_ $cal(T)$ if, for some free sides, the constraints of the record hold at the proportion of $cal(T)$, its tiles are those of $cal(T)$, and each of its placements has the orientation chosen for its tile.
  A complete admissible record that yields $cal(T)$ places at every stage the tile at the anchor of the first tier whose floor does not extend in $cal(T)$, provided that at every crossing of $cal(T)$ the tile to the lower right of the crossing is placed before the tile to its upper left.
  In particular a tiling without crossings is yielded by at most one complete admissible record for each choice of orientations.
] <prop:representative>

#proof[
  Consider a placement of the record at a tier $T_i$ of the current staircase.
  Every tier $T_j$ with $j < i$ has a floor that extends.
  This is so if $j = i - 1$ and the tile placed is as high as the wall of $T_i$, since the top side of that tile continues the floor to the right.
  Otherwise $T_j$ becomes stale by this placement, and can cease to be stale only if its floor is lengthened by a tile as high as the wall at the next tier, whose top side then continues the floor to the right, so that the floor extends; and a stale tier is never removed, so that the record could not be complete.
  Suppose that the floor of $T_i$ extends, and let $Q$ be its right end.
  The tile that makes it extend is still to be placed, since points of its interior lie in the strip of the next tier; so its interior lies in the region of the staircase, which contains no point to the left of $Q$ and below the floor, by @obs:strips.
  Its left side is therefore at the abscissa of $Q$; let $U$ be this tile, whose top left corner is $Q$.
  If the tile placed at $T_i$ is narrower than the floor, the remainder of the floor is started, and it remains so until a tile $V$ is placed whose bottom side ends at $Q$; if it is as wide as the floor, it is itself such a tile $V$.
  As long as the floor is started, $U$ cannot be placed, since it would lengthen the floor.
  Hence $V$ is placed before $U$, and $Q$ is a crossing with $V$ to its upper left and $U$ to its lower right, contrary to the hypothesis.
  So the floor of $T_i$ does not extend, and $T_i$ is the first tier with that property.
  The record is thus determined by $cal(T)$ and the orientations.
]

The record constructed in the proof of @prop:complete is of this kind, and the same construction gives one record for each choice, at each crossing, of which of the two tiles is placed first.

#proposition[
  Let $cal(T)$ be a similar tiling with $k$ crossings, with a choice of orientation for each tile, a tile that is not a square having the orientation of its shape.
  For every set $X$ of crossings of $cal(T)$ there is exactly one complete admissible record that yields $cal(T)$ and in which the tile to the upper left of a crossing is placed before the tile to its lower right exactly at the crossings of $X$.
  Hence exactly $2^k$ complete admissible records yield $cal(T)$.
] <prop:multiplicity>

#proof[
  Say that a floor _$X$-extends_ if it extends in $cal(T)$ and its right end is not a crossing in $X$.
  We show that a record as in the statement places, at every stage, the tile at the anchor of the first tier whose floor does not $X$-extend, which determines it.
  Consider a placement at a tier $T_i$.
  By the proof of @prop:representative, the floor of every tier $T_j$ with $j < i$ extends, and from this placement on $T_j$ is stale, or the tile placed is as high as the wall and $j = i - 1$; in either case no tile is placed at $T_j$ before the tile $U_j$ whose top left corner is the end $Q_j$ of the floor.
  If $Q_j$ is a crossing, the tile to its upper left has points of its interior in the strip of $T_j$ and of no other tier, so that it is placed at $T_j$ or at a tier that replaces it, after $U_j$, and $Q_j$ is not in $X$; hence the floor of $T_j$ $X$-extends.
  If the floor of $T_i$ extends, the proof of @prop:representative shows that its end is a crossing at which the tile to the upper left is placed first, hence a crossing in $X$; so the floor of $T_i$ does not $X$-extend.

  For the existence, we repeat the construction of @prop:complete with the first tier whose floor does not $X$-extend, and with the fourth condition of @def:state replaced by the condition that the floor of every stale tier $X$-extends and the floor of no started tier does.
  The proof of @prop:extension applies with the following changes.
  The two verifications that the proof of @prop:extension leaves to the formal proof do not involve the notion of extending, and are unchanged.
  If $w > L$, the floor of $T_i$ extends, as shown there, and its end lies in the interior of the bottom side of the tile $Q$ at the anchor, so that it is not a crossing; the floor then $X$-extends, contrary to the choice of $T_i$.
  The proof that $h <= M$ uses only the fact that the floor of $T_(i - 1)$ extends.
  The placement is allowed, since the floor of a stale tier $X$-extends, and the floor of $T_(i - 1)$ $X$-extends while that of a started tier does not.
  The orientation is the one chosen for $Q$; when $Q$ is a square, the sizes and the equations of the two orientations coincide.
  After the placement, the started tier, if any, has a floor that ends where the floor of $T_i$ did, and so does not $X$-extend.
  This gives a complete admissible record $rho_X$ that yields $cal(T)$.

  Let $Q$ be a crossing, $V$ the tile to its upper left and $U$ the tile to its lower right.
  Suppose that $U$ is placed before $V$ in $rho_X$, at a tier $T_i$.
  The interior of $V$ lies in the region of the staircase, which, by @obs:strips, contains no point to the left of the anchor of $T_i$ and below the top of its wall; so $U$ is as high as the wall. Then $i > 0$, since $Q$ is not on the boundary of the square, the floor of $T_(i - 1)$ ends at $Q$, and it extends.
  As $T_(i - 1)$ comes before the tier chosen, its floor $X$-extends, and $Q$ is not in $X$.
  Suppose that $V$ is placed before $U$, at a tier $T_i$.
  The interior of $U$ lies in the region of the staircase, which contains no point below the floor of $T_i$ and to the left of its end; so $V$ is as wide as the floor, which ends at $Q$ and extends.
  By the choice of the tier the floor does not $X$-extend, and $Q$ is in $X$.
  So $rho_X$ is as in the statement.
  The records $rho_X$ are distinct, since the order in which a record that yields $cal(T)$ places the tiles is determined by the record and $cal(T)$, since each tile is the one at the anchor of its placement.
]

Neither proposition has been formalised.
For $X$ empty the record of @prop:multiplicity is that of @prop:complete, so that a tiling without crossings has exactly one record for each choice of orientations, and for a tiling by squares the choice of orientations is free.
This is one half of what the agreement of the number of placement sequences with the Baxter numbers, observed in @sec:mosaic, would require; the other half, that every complete admissible sequence is that of a tiling by rectangles without crossings, and that two such tilings have the same sequence exactly when they are mosaic equivalent, is not proved.
The computation agrees with @prop:multiplicity: for $n <= 12$ and each $k$, the records of the tilings with $k$ crossings are $2^k$ times as many as these tilings.
The search for tilings keeps the record described in @prop:representative, which it recognises by rebuilding the sequence from the exact order of the coordinates.

The values of @tab:tbc were checked as follows.
For $n <= 8$ all three sequences, the number of tilings fixed by each symmetry and the numbers for each single proportion agree with an independent program, which represents tilings as sets of rectangles with coordinates in the number field and examines all $2^n$ orientation vectors.
For $n <= 10$ they agree with a run in which every record is solved by the direct method and every comparison of coordinates is exact.
For $n <= 9$ the values of $t(n)$ agree with a count of the tilings through their plane networks, described in @sec:full-side, which does not use the staircase construction and is carried out in floating-point arithmetic.
For $n <= 12$ the number of classes obtained from canonical representatives agrees with the number given by Burnside's lemma from the tilings fixed by each symmetry, and the number of records agrees with the count $sum 2^k$ described above.
The values of all three sequences for $n = 11$ and $n = 12$ depend on the search alone.

Some features of the table can be proved.

#proposition[
  + The number $t(n)$ has the parity of the number of tilings of the unit square by $n$ squares.
  + A similar tiling of the square that is fixed by the reflection in a diagonal consists of squares.
  + A similar tiling of the square of proportion $x > 1$ that is fixed by a quarter turn has a crossing at the centre of the square, and its number of tiles is a multiple of four.
] <prop:symmetric>

#proof[
  We prove the second statement first.
  The reflection fixes two corners of the square, hence the tile that contains one of them, and a rectangle fixed by the reflection in a diagonal through one of its corners is a square.
  For the first statement, transposition is an involution on the finite set of similar tilings of the unit square with $n$ tiles and proportion $x > 1$, and it has no fixed point among them, by the second statement.
  For the third, the centre of the square cannot lie in the interior of a tile, since the tile would be mapped to itself by the quarter turn, which a rectangle of proportion $x > 1$ is not; nor can it lie in the relative interior of a side of a tile, since the quarter turn would map that side to a perpendicular segment through the centre, which meets the interior of a tile and is not contained in the sides of the tiles.
  So the centre is a corner of every tile that contains it; there are four such tiles, and the centre is a crossing.
  No tile is then fixed by the half turn, so the quarter turn permutes the tiles in orbits of four.
]

Accordingly $t(n)$ is odd for $n = 1$, $4$, $9$ and $12$ in the range computed, and tilings fixed by a quarter turn occur there only for $n = 1$, $4$, $8$, $9$ and $12$; a tiling by squares fixed by a quarter turn has a tile centred at the centre of the square or a crossing there, so that its number of tiles is congruent to $0$ or $1$ modulo $4$.
Tilings with a symmetry are rare: there are $2629349$ of them among the $9213388789$ tilings with twelve tiles, and $8 b(12) slash t(12) = 1.0003$.

#proposition[
  For every $n >= 6$, $c(n) > a(n)$.
] <prop:bags>

#proof[
  Let $cal(T)$ be a similar tiling of the square with $n - 3$ tiles in which two tiles have different short sides $s != s'$.
  Cutting the first of these tiles into four, as in the proof of @prop:subdivision, gives a tiling with $n$ tiles whose bag is obtained from that of $cal(T)$ by replacing one copy of $s$ by four copies of $s slash 2$; cutting the second gives the bag in which one copy of $s'$ is replaced by four copies of $s' slash 2$.
  The two bags have the same proportion, and they differ: the sums of the short sides differ by $s - s'$.
  Tilings with tiles of two sizes exist for every number of tiles from three onwards: for $m >= 2$, a wide tile of width $1$ above a row of $m$ congruent wide tiles of width $1 slash m$ is a similar tiling of the square of proportion $(m + 1) slash m$ with $m + 1$ tiles.
]

For $n <= 5$ every proportion has a single bag.
For larger $n$ nearly every proportion still has a single bag: the quotient $c(n) slash a(n)$ rises only from $1.020$ for six tiles to $1.056$ for twelve.
The proportion $2$ has the most bags, and the most classes, for every $n$ from $8$ to $11$.

#conjecture[
  The sequence $t(n + 1) slash t(n)$ is increasing for $n >= 5$.
] <conj:growth-quotients>

#conjecture[
  The quotient $8 b(n) slash t(n)$ tends to $1$ as $n$ tends to infinity.
] <conj:growth-symmetry>

#conjecture[
  The sequence $t(n)^(1 slash n)$ converges.
] <conj:growth-rate>

@conj:growth-quotients holds for $5 <= n <= 11$.
For @conj:growth-symmetry, the quotient $8 b(n) slash t(n)$ decreases for $3 <= n <= 12$, to $1.0003$.
For @conj:growth-rate, the quotient of $t(n)$ by $2^n M(n)$, with $M(n)$ as in @prop:upper, takes the values $0.2850$, $0.2787$, $0.2838$, $0.2859$, $0.2882$, $0.2898$, $0.2911$ and $0.2920$ for $n = 5, dots, 12$, which suggests the rate $27 slash 2$ of $2^n M(n)$; but the limit, if it exists, is smaller than $27 slash 2$ by @prop:deficit, so that this quotient eventually tends to zero.
The three statements are independent of one another as far as we know.

#heading(numbering: none)[Use of AI Systems]

This project was carried out with responsible use of AI systems.
The author formulated, implemented and proved an initial version of Sections 1-4, which AI systems optimised and improved upon.
The results of Section 5 were found by computation, and the propositions/conjectures of Section 5 were formulated and proved by AI systems on individual request by the author.
An initial version of the solution methods for linear systems in Appendix B were proposed by the author, and were then autonomously improved by AI systems with the objective of optimising various aspects of the search algorithm.
Lean formalisation was carried out by AI systems on general request by the author.
Properties and conjectures in Appendix D were autonomously formulated by AI systems, on request by the author for each theme of investigation.
The paper was written and reviewed by AI systems --- under the author's own direction, supervision, and revision --- based on the fullness of project data: development transcripts, source code, documentation, version history, test suites, and benchmarking results.

#bibliography("refs.bib", style: "ieee")

#show: appendix

= Catalogue of tilings <app:catalogue>

@fig:five and @fig:six show one tiling for each proportion achievable with five and with six tiles, labelled by proportion; the cases of three and four tiles are in @fig:three and @fig:four.
The tiling shown for a proportion is the first found by one run of the search, and is in general one of several.

#figure(
  image("figures/five-tiles.svg", width: 100%),
  caption: [One tiling for each of the $51$ proportions achievable with five tiles.],
) <fig:five>

#figure(
  image("figures/six-tiles.svg", width: 100%),
  caption: [One tiling for each of the $245$ proportions achievable with six tiles.],
) <fig:six>

= Solving the linear systems <app:solving>

This appendix defines the two forms of the search described in @sec:solving and proves @prop:search.
The direct search solves the system for each record separately; the incremental search eliminates along the tree of records and verifies its candidates numerically.
The arithmetic in both is performed by routines that are not part of what is proved: the statements hold for any routines that meet the specifications of @def:primitives and @def:numerics.

== Linear forms <sec:forms>

For a main rectangle of sides in the ratio $a slash b$, with $a$ and $b$ positive integers, the height is normalised to $H = 1$ and the width $W$ is kept as an unknown, to be compared with $a slash b$ at the end.
Every floor and wall arising along a record is then a linear form in $1$, $W$ and the free sides, whose coefficients are polynomials in the proportion divided by a power of it.

#definition(name: [linear forms])[
  A _linear form_ is a pair $f = (d, c)$ of an integer $d >= 0$ and a sequence $c = (c_0, c_1, c_2, dots)$ of polynomials in $ZZ[x]$; it stands for the expression
  $ (c_0 + c_1 W + c_2 s_1 + c_3 s_2 + dots.c) / x^d. $
  The sum and the difference of $(d, c)$ and $(d', c')$ have exponent $D = max(d, d')$ and coefficients $c_j x^(D - d) plus.minus c'_j x^(D - d')$; the product of $(d, c)$ with $x$ is $(d - 1, c)$ if $d > 0$ and $(0, x c)$ if $d = 0$; and the quotient of $(d, c)$ by $x$ is $(d + 1, c)$.
  With these operations the linear forms are an arithmetic of lengths.
  For an integer $k >= 0$ and real numbers $x != 0$, $W$ and $s_1, dots, s_k$, the _numerator_ and the _value_ of $f$ are
  $ nu_k (f) := c_0 (x) + c_1 (x) W + sum_(j = 1)^k c_(j + 1) (x) s_j, quad "val"_k (f) := nu_k (f) / x^d. $
  The _symbolic system_ of a record $rho$ consists of the positivity constraints and of the equations obtained by placing $rho$ on the initial staircase whose floor is the form $W$ and whose wall is the form $1$, with the forms $s_1, s_2, dots$ as free sides.
] <def:forms>

Evaluating the forms recovers the constraints of @def:system, so that the symbolic system may be used in their place.

#proposition[
  Let $rho$ be a record with $k$ inside placements, and let $x != 0$, $W$ and $s = (s_1, s_2, dots)$ be real numbers.
  Then $(W, 1, s)$ satisfy the constraints of $rho$ at $x$ if and only if $"val"_k (f) > 0$ for every positivity constraint $f$ of the symbolic system of $rho$ and $"val"_k (g) = 0$ for every equation $g$ of it.
] <prop:forms>

#proof[
  For $x != 0$ the map $"val"_k$ is a homomorphism from the linear forms to the real numbers: this is a direct verification for each of the four operations, in which numerators are brought to the common power of $x$.
  It sends the form $W$ to $W$, the form $1$ to $1$, and the form $s_j$ to $s_j$ for $j <= k$.
  Since placing commutes with homomorphisms, the positivity constraints and the equations of $rho$ on the real initial staircase of $W$ and $1$, with free sides the values of the forms $s_j$, are the values of those of the symbolic system.
  Only the first $k$ free sides are used, and their values are $s_1, dots, s_k$.
]

== The direct method <sec:direct>

The direct form of the search treats each record separately and uses exact arithmetic throughout.
Its arithmetic is performed by three routines, which are not part of what is proved here: the statements below hold for any routines that meet the following specifications.

#definition(name: [exact routines])[
  The _exact routines_ are the following, with their assumed specifications.
  + _Elimination._ Given a square matrix $A$ over $ZZ[x]$, of size $m$, and a vector $c in ZZ[x]^m$, the routine either fails or returns a polynomial $D$ and polynomials $N_1, dots, N_m$.
    In the second case there is $lambda in ZZ[x]$ such that $D = lambda det A$ and $N_i = lambda det A_i$ for every $i$, where $A_i$ is the matrix $A$ with its $i$-th column replaced by $c$.
  + _Roots._ Given a polynomial $q in ZZ[x]$, the routine returns a finite set $"roots"(q)$ of real numbers.
    If $q != 0$, this is the set of real numbers $r >= 1$ with $q(r) = 0$.
  + _Signs._ Given a real number $r$ and a polynomial $q in ZZ[x]$, the routine returns a sign $"sign"(r, q)$, which is $-1$, $0$ or $1$.
    If $r$ belongs to $"roots"(q')$ for some polynomial $q'$, this is the sign of the real number $q(r)$.
] <def:primitives>

Nothing is assumed of the elimination when it fails.
In the implementation, the elimination is the fraction-free Bareiss elimination @bareiss1968 with back-substitution, for which $lambda = plus.minus 1$, and it fails when it finds no pivot.
The roots are obtained by factorising $q$ into irreducible factors over $ZZ$ and isolating the real roots of each factor in $[1, infinity)$ by Descartes' rule of signs with bisection @collins1976, so that each root is identified by its minimal polynomial and its position among the roots of that polynomial; factorisation proceeds by reduction modulo a prime exceeding twice the Landau–Mignotte bound @mignotte1974 on the coefficients of the factors, using Berlekamp's method @berlekamp1970, followed by recombination of the modular factors by trial division.
The sign of $q$ at a root $r$ is zero if and only if the minimal polynomial of $r$ divides $q$, and is otherwise found by evaluating $q$ on an isolating interval for $r$, refined until the value is separated from zero.

#definition(name: [direct method])[
  Let $a$ and $b$ be integers and let $rho$ be a complete admissible record, with $k$ inside placements.
  Let $g_1, dots, g_(k + 1)$ be the equations of its symbolic system, as given by @prop:count, and write $g_r = (d_r, c^((r)))$.
  Let $A$ be the square matrix of size $k + 1$ with entries $A_(r j) := c^((r))_(j + 1)$ for $j <= k$ and $A_(r, k + 1) := c^((r))_1$, and let $c$ be the vector with entries $c_r := -c^((r))_0$, so that the columns of $A$ correspond to the unknowns $s_1, dots, s_k, W$.
  The _direct method_ treats $rho$ as follows.
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

#proposition[
  Let $q in ZZ[x]$ be such that the coefficients of $q(x + 1)$ are all non-negative or all non-positive, and its constant coefficient is not zero.
  Then $q(r) != 0$ for every real number $r >= 1$.
] <prop:noroot>

#proof[
  Let $q(x + 1) = sum_j q_j x^j$, so that $q(r) = q_0 + sum_(j >= 1) q_j (r - 1)^j$ with $r - 1 >= 0$.
  If the $q_j$ are non-negative then $q_0 > 0$ and the sum is non-negative, so $q(r) > 0$; if they are non-positive then similarly $q(r) < 0$.
]

With routines that meet their specifications, the method reports only solutions of the system, and it reports all of them when it counts no singular situation.

#proposition[
  Let $a$ and $b != 0$ be integers, and let $rho$ be a complete admissible record.
  + Every $r in "Ref"_(a, b) (rho)$ satisfies $r >= 1$, and there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$.
  + If the direct method counts no singular situation for $rho$ and does not flag it as constant, then conversely every real number $r >= 1$ for which there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$ belongs to $"Ref"_(a, b) (rho)$.
] <prop:solve>

#proof[
  Let $k$ be the number of inside placements of $rho$, and keep the notation of @def:reference.
  For a real number $r != 0$ and real numbers $W$ and $s_1, dots, s_k$, write $z := (s_1, dots, s_k, W)$.
  By the definition of $A$ and $c$, the numerator of the equation $g_i$ is $nu_k (g_i) = (A(r) z)_i - c_i (r)$.
  For $r > 0$ a value has the sign of its numerator, so that, by @prop:forms, $(W, 1, s)$ satisfy the constraints of $rho$ at $r$ if and only if $A(r) z = c(r)$ and $nu_k (f) > 0$ for every positivity constraint $f$ of the symbolic system.
  Two facts about the matrix $A$ over the ring $ZZ[x]$ are used, both consequences of the identity between a matrix and its adjugate: $A dot.op (det A_1, dots, det A_(k + 1))^top = (det A) c$, and, for every real vector $z$ with $A(r) z = c(r)$, $(det A)(r) z_i = (det A_i)(r)$ for every $i$.

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
  The record is not flagged as constant, so $F_rho != 0$; the test in the third step fails, by @prop:noroot; hence the fourth step is reached and $r in "roots"(F_rho)$.
  No singular situation is counted, so $"sign"(r, D) != 0$.
  Finally $Q_f (r) = D(r) nu_k (f)$ with $nu_k (f) > 0$, so $Q_f (r)$ has the sign of $D(r)$, and $r$ is reported.
]

The search verifies the hypothesis of the second statement.

#definition(name: [regular record])[
  Let $a$ and $b$ be integers.
  A complete admissible record is _regular_ for $(a, b)$ if the direct method counts no singular situation for it and does not flag it as constant.
  For an integer $n >= 0$, the direct search _reports_ the numbers of
  $ "Ref"_n (a, b) := union.big_rho "Ref"_(a, b) (rho), $
  where $rho$ ranges over the complete admissible records for $n$ tiles, in which moreover the first tile is wide if $a = b$.
  The direct search for $n$ tiles is _certified_ if all these records are regular for $(a, b)$.
] <def:regular>

A record is thus regular if the elimination succeeds, $F_rho$ is not zero, and $D$ does not vanish at any root of $F_rho$ in $[1, infinity)$; the last condition is vacuous when the test in the third step succeeds.

#proposition[
  Let $a, b >= 1$ and $n >= 0$ be integers.
  Then $"Ref"_n (a, b) subset.eq P_n (a, b)$.
  If the direct search for $n$ tiles is certified, then $"Ref"_n (a, b) = P_n (a, b)$.
] <prop:reference>

#proof[
  Let $r in "Ref"_(a, b) (rho)$ for a complete admissible record $rho$ for $n$ tiles.
  By @prop:solve, $r >= 1$ and $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$ for some $s$, so by @prop:sound there is a similar tiling of $[0, a slash b] times [0, 1]$ of proportion $r$ with $n$ tiles.
  Hence $r in P_n (a slash b, 1) = P_n (a, b)$, by @prop:scaling.
  Conversely, let $r in P_n (a, b) = P_n (a slash b, 1)$.
  If $a != b$, @prop:complete gives a complete admissible record $rho$ for $n$ tiles and $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$; if $a = b$, @prop:square gives the same with the first tile wide in $rho$.
  If the search is certified, $rho$ is regular, and $r in "Ref"_(a, b) (rho)$ by @prop:solve.
]

== Eager elimination <sec:eager>

The direct search treats every record independently, each at the cost of a symbolic elimination; when the main rectangle is a square there are $2^(n - 1) B(n)$ of them for every $n <= 13$, where $B(n)$ is the $n$-th Baxter number, by the count reported in @sec:mosaic.
The incremental search shares work between records with a common beginning, and replaces nearly all exact sign determinations by certified numerical ones.
A record that it cannot decide is passed to the direct method, so that its correctness rests on that of the direct method only for such records.


Records are explored depth first, as paths in the tree of admissible sequences, and the linear forms for floors and walls are maintained along the current path.
Instead of collecting equations to be solved at the leaves, each equation is used at once to eliminate one unknown from every floor and wall of the current staircase.
To keep the system homogeneous, the main rectangle is given sides $a t$ and $b t$ for an unknown scale $t$.

#definition(name: [homogeneous system])[
  Let $R$ be an integral domain and $X$ a unit of $R$; in the method, $R = ZZ[x, x^(-1)]$ and $X = x$.
  A _form_ over $R$ is a sequence $F = (F_0, F_1, F_2, dots)$ of elements of $R$; it stands for the expression $F_0 t + F_1 s_1 + F_2 s_2 + dots.c$.
  The forms over $R$ are an arithmetic of lengths: sums and differences are taken coefficient by coefficient, and the product and the quotient by $x$ multiply every coefficient by $X$ and by $X^(-1)$.
  We write $u_j$ for the form whose coefficient of index $j$ is $1$ and whose other coefficients are zero.
  For integers $a$ and $b$, the _homogeneous system_ of a record $rho$ consists of the positivity constraints $kappa_1, kappa_2, dots$ and of the equations $e_1, e_2, dots$ obtained by placing $rho$ on the initial staircase with floor $a u_0$ and wall $b u_0$, with free sides $u_1, u_2, dots$.
  For a homomorphism $chi$ from $R$ to a field $K$, a form $F$ over $R$, an integer $N >= 1$ and $v = (v_0, dots, v_(N - 1)) in K^N$, the _value_ of $F$ at $v$ is $F[v] := sum_(j < N) chi(F_j) v_j$; for a form $G$ over $K$ we similarly write $G[v] := sum_(j < N) G_j v_j$.
] <def:hom>

For a record with $k$ inside placements, values are always taken with $N = k + 1$, so that $v_0$ is the value of the scale and $v_1, dots, v_k$ are the free sides.
The homogeneous system at scale one is the system of the main rectangle of sides $a$ and $b$, which is that of the main rectangle of sides $a slash b$ and $1$ up to a change of scale.

#proposition[
  Let $rho$ be a record with $k$ inside placements, let $a$ and $b$ be integers, let $chi$ be a homomorphism from $R$ to the real numbers with $alpha := chi(X) > 0$, and let $v in RR^(k + 1)$ with $v_0 = 1$.
  Then $(a, b, (v_1, dots, v_k))$ satisfy the constraints of $rho$ at $alpha$ if and only if $kappa_q [v] > 0$ for every positivity constraint and $e_i [v] = 0$ for every equation of the homogeneous system of $rho$.
  Moreover, if $b >= 1$, then for every real number $alpha > 0$ there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $alpha$ if and only if there is $s'$ such that $(a, b, s')$ satisfy them.
] <prop:hom>

#proof[
  The map $F |-> F[v]$ is a homomorphism from the forms over $R$ to the real numbers, with proportion $alpha$: it is additive, and $chi(X F_j) = alpha chi(F_j)$ and $chi(X^(-1) F_j) = chi(F_j) slash alpha$.
  It sends $a u_0$ to $a$, $b u_0$ to $b$, and $u_j$ to $v_j$ for $1 <= j <= k$.
  The first statement follows as in the proof of @prop:forms, since placing commutes with homomorphisms and only the first $k$ free sides are used.
  For the second, multiplication by a real number $c > 0$ is a homomorphism from the real numbers to themselves, which preserves the sign of every number.
  Hence $(W, H, s)$ satisfy the constraints of $rho$ at $alpha$ if and only if $(c W, c H, c s)$ do, and the statement follows with $c = b$.
]

The pass along a record keeps, besides the staircase, the coefficient by which the last unknown was eliminated, by which the next elimination divides.

#definition(name: [symbolic pass])[
  A _stage_ is a triple $(S, pi, k)$ of a staircase $S$ over the forms over $R$, a _pivot_ $pi in R$ with $pi != 0$, and an integer $k >= 0$; the _initial stage_ for integers $a$ and $b$ consists of the initial staircase with floor $a u_0$ and wall $b u_0$, the pivot $1$ and $k = 0$.
  An _elimination_ is a triple $epsilon = (E, m, pi)$ of a form $E$ over $R$, an index $m$ and an element $pi != 0$ of $R$.
  It _divides_ a form $F$ _exactly_ if $pi$ divides $E_m F_j - F_m E_j$ in $R$ for every $j$, and $epsilon(F)$ then denotes the form with coefficients $(E_m F_j - F_m E_j) slash pi$.
  Let $rho = (p_1, dots, p_ell)$ be a record with $ell >= 1$.
  A _successful pass_ along $rho$ is a sequence of stages $Sigma_0, dots, Sigma_(ell - 1)$, where $Sigma_0$ is the initial stage, such that the following holds for every $j <= ell$, with $Sigma_(j - 1) = (S, pi, k)$.
  The tier of $p_j$ exists in $S$.
  Let $S^+$ be the staircase obtained by placing $p_j$ on $S$ with free side $pi u_(k + 1)$, and let $k^+$ be $k + 1$ if $p_j$ is inside and $k$ otherwise.
  The positive quantity $sigma_j$ of $p_j$ on $S$, with that free side, is the _size recorded_ with $p_j$.
  + If $j = ell$, the placement $p_ell$ has an equation $E$ on $S$, which is the _final equation_ of the pass.
  + If $j < ell$ and $p_j$ has no equation, then $Sigma_j = (S^+, pi, k^+)$.
  + If $j < ell$ and $p_j$ has an equation $E$ on $S$, there is an index $m$ with $1 <= m <= k^+$ and $E_m != 0$ such that the elimination $epsilon = (E, m, pi)$ divides exactly every floor and wall of $S^+$, and $Sigma_j = (epsilon(S^+), E_m, k^+)$, where $epsilon(S^+)$ is obtained by applying $epsilon$ to every floor and wall of $S^+$; the elimination $epsilon$ is _recorded_ with $p_j$.
] <def:elimination>

A tile placed inside receives as its free side the next unknown multiplied by the current pivot, and each equation removes one unknown from the staircase, at the cost of multiplying every length by the new pivot and dividing it by the old one.
A stage therefore represents lengths up to the factor of its pivot.
The method makes the pass deterministic by a rule for the choice of the index $m$; the implementation takes an unknown whose coefficient in $E$ has the smallest span of exponents, and the first such unknown in case of a tie.
The pass _fails_, in the method, when an arithmetic operation exceeds the range of the machine integers, when the rule yields no index $m$ as required, when a division is not exact, and when the staircase is not emptied by the last placement of the record, through a full placement, and by no earlier one.
Nothing is assumed about the first two causes, nor is anything proved about how often the pass fails: the statements below concern successful passes, and a record on which the pass fails is passed to the direct method.
The third cause never occurs, by @prop:exact.

The forms of a stage are related to those of the homogeneous system, on which no elimination has been made, over any field in which the pivots do not vanish.

#definition(name: [carrying])[
  Let $psi$ be a homomorphism from $R$ to a field $K$; it is applied to forms coefficient by coefficient.
  For an elimination $epsilon = (E, m, pi)$ with $psi(pi) != 0$, let $gamma_epsilon$ be the map on the forms over $K$ given by
  $ gamma_epsilon (G)_j := (psi(E_m) G_j - G_m psi(E_j)) / psi(pi). $
  An _elimination chain_ over $psi$ consists of eliminations $epsilon_1, dots, epsilon_r$, with $epsilon_i = (E_i, m_i, pi_(i - 1))$, and of forms $e_1, dots, e_r$ over $R$, its _originals_, such that $pi_0 = 1$, $pi_i = (E_i)_(m_i)$ for $i < r$, $psi(pi_(i - 1)) != 0$ for $i <= r$, and
  $
    psi(E_i) = Gamma_(i - 1) (psi(e_i)) quad "for" i <= r, quad "where" Gamma_i := gamma_(epsilon_i) compose dots.c compose gamma_(epsilon_1).
  $
  Its _current pivot_ is $pi_r := (E_r)_(m_r)$, or $1$ if $r = 0$.
  A form over $K$ is _carried_ through $epsilon_1, dots, epsilon_r$ by applying $Gamma_r$.
] <def:chain>

Each $gamma_epsilon$ is linear over $K$, so it commutes with sums, differences and the multiplication by $psi(X)$ and by its inverse: it is a homomorphism of the arithmetic of the forms over $K$ to itself, and so is each $Gamma_i$.
If $epsilon$ divides $F$ exactly and $psi(pi) != 0$, then $psi(epsilon(F)) = gamma_epsilon (psi(F))$.
Nothing in the definition of a chain requires the current pivot to have a non-zero image.

#proposition[
  Let $psi$ be a homomorphism from $R$ to a field $K$, and consider a successful pass along a record $rho = (p_1, dots, p_ell)$, with final equation $E_"fin"$, whose recorded eliminations are, in order, $epsilon_1, dots, epsilon_r$ with $epsilon_i = (E_i, m_i, pi_(i - 1))$.
  Suppose that $psi((E_i)_(m_i)) != 0$ for every $i <= r$.
  Then the homogeneous system of $rho$ has $r + 1$ equations $e_1, dots, e_(r + 1)$, and
  + the eliminations $epsilon_1, dots, epsilon_r$ form an elimination chain over $psi$ with originals $e_1, dots, e_r$, and $psi(pi_r) != 0$;
  + $psi(E_"fin") = Gamma_r (psi(e_(r + 1)))$;
  + for every $q <= ell$, the size recorded with $p_q$ satisfies $psi(sigma_q) = Gamma_(r(q)) (psi(kappa_q))$, where $r(q)$ is the number of eliminations recorded with $p_1, dots, p_(q - 1)$.
] <prop:trace>

#proof[
  Let $hat(S)_j$ be the staircase obtained by placing $p_1, dots, p_j$ on the initial staircase with floor $a u_0$ and wall $b u_0$, with free sides $u_1, u_2, dots$, so that the $kappa_q$ and the $e_i$ are the positive quantities and the equations of the placements on these staircases.
  We show by induction on $j < ell$ that the stage $Sigma_j = (S, pi, k)$, reached after $r'$ eliminations, has the following properties: the eliminations $epsilon_1, dots, epsilon_(r')$ form a chain over $psi$ whose originals are the equations of the full placements among $p_1, dots, p_j$ and whose current pivot is $pi$, with $psi(pi) != 0$; the staircase $S$ has the tiers of $hat(S)_j$, and $psi(F) = Gamma_(r') (psi(hat(F)))$ for every floor or wall $F$ of $S$ and the corresponding floor or wall $hat(F)$ of $hat(S)_j$; the number of inside placements among $p_1, dots, p_j$ is $k$; and $Gamma_(r') (u_i) = psi(pi) u_i$ for every $i > k$.
  For $j = 0$ these hold with $r' = 0$, $Gamma_0$ the identity and $pi = 1$.

  Suppose that they hold for $Sigma_(j - 1) = (S, pi, k)$, and consider the placement $p_j$.
  The maps $F |-> psi(F)$ and $F |-> Gamma_(r') (psi(F))$ are homomorphisms from the forms over $R$ to the forms over $K$.
  The first sends the staircase $S$ and the free side $pi u_(k + 1)$ to the same staircase and the same form as the second sends $hat(S)_(j - 1)$ and the free side $u_(k + 1)$, by the induction hypothesis; the last property is used for $i = k + 1$.
  Since placing commutes with homomorphisms, $psi(F) = Gamma_(r') (psi(hat(F)))$ for every floor or wall $F$ of $S^+$ and the corresponding one of $hat(S)_j$, the size recorded satisfies $psi(sigma_j) = Gamma_(r') (psi(kappa_j))$, and $p_j$ has an equation $E$ on $S$ exactly if it has an equation $e$ on $hat(S)_(j - 1)$, in which case $psi(E) = Gamma_(r') (psi(e))$.
  This proves the third statement for $q = j$, with $r(j) = r'$, and, when $j = ell$, the second statement and the count of the equations.
  Let $j < ell$.
  If $p_j$ has no equation, $Sigma_j = (S^+, pi, k^+)$ and the properties hold for it, with the same chain.
  If $p_j$ has an equation $E$ and $epsilon = (E, m, pi)$ is the elimination recorded, then $epsilon$ with the original $e$ extends the chain, because $psi(pi) != 0$ and $psi(E) = Gamma_(r') (psi(e))$; the new current pivot is $E_m$, and $psi(E_m) != 0$ by hypothesis.
  For a floor or wall $F$ of $S^+$, exactness gives $psi(epsilon(F)) = gamma_epsilon (psi(F)) = gamma_epsilon (Gamma_(r') (psi(hat(F))))$, which is the form $psi(hat(F))$ carried through the extended chain.
  Finally, for $i > k^+$ we have $i != m$, so the coefficient of index $m$ of $u_i$ is zero and $gamma_epsilon (psi(pi) u_i) = psi(E_m) psi(pi) u_i slash psi(pi) = psi(E_m) u_i$.
  The properties therefore hold for $Sigma_j$, and the first statement is the first property for $j = ell - 1$.
]

The properties of elimination chains that are used below are the following; they do not depend on the chain arising from a pass.

#proposition[
  Let $epsilon_1, dots, epsilon_r$, with $epsilon_i = (E_i, m_i, pi_(i - 1))$, be an elimination chain over $psi$ with originals $e_1, dots, e_r$ and current pivot $pi_r$, let $G$ be a form over $K$, let $N >= 1$ and let $v in K^N$.
  + There are $c_1, dots, c_r in K$ such that $Gamma_r (G) = psi(pi_r) G + sum_(l <= r) c_l psi(e_l)$.
  + For every $i <= r$ there are $c_1, dots, c_(i - 1) in K$ such that $psi(E_i) = psi(pi_(i - 1)) psi(e_i) + sum_(l < i) c_l psi(e_l)$.
  + $Gamma_r (G)_(m_i) = 0$ for every $i <= r$, and $psi((E_i)_(m_l)) = 0$ for all $l < i <= r$.
  + If $psi(e_l)[v] = 0$ for every $l <= r$, then $Gamma_r (G)[v] = psi(pi_r) G[v]$.
  + $psi(e_l)[v] = 0$ for every $l <= r$ if and only if $psi(E_l)[v] = 0$ for every $l <= r$.
  + If $psi((E_i)_(m_i)) != 0$ for every $i <= r$, the indices $m_1, dots, m_r$ are pairwise distinct.
] <prop:chain>

#proof[
  All statements but the last are proved by induction on $r$, and are clear for $r = 0$, where $Gamma_0$ is the identity and $pi_0 = 1$.
  Let $r >= 1$, write $epsilon_r = (E, m, pi)$ with $pi = pi_(r - 1)$, and let $G' := Gamma_(r - 1) (G)$, so that
  $ Gamma_r (G) = (psi(E_m) G' - G'_m psi(E)) / psi(pi), quad psi(E) = Gamma_(r - 1) (psi(e_r)). $
  For the first statement, the induction hypothesis gives $G' = psi(pi) G + sum_(l < r) c'_l psi(e_l)$ and $psi(E) = psi(pi) psi(e_r) + sum_(l < r) d_l psi(e_l)$, and the latter is also the second statement for $i = r$; for $i < r$ the second statement is that of the chain $epsilon_1, dots, epsilon_(r - 1)$.
  Substituting,
  $ Gamma_r (G) = psi(E_m) G - G'_m psi(e_r) + sum_(l < r) (psi(E_m) c'_l - G'_m d_l) / psi(pi) thin psi(e_l), $
  which is of the form stated, since $pi_r = E_m$.
  For the third, the coefficient of index $m$ of $Gamma_r (G)$ is $(psi(E_m) G'_m - G'_m psi(E_m)) slash psi(pi) = 0$; and for $i < r$ the coefficients of index $m_i$ of $G'$ and of $psi(E) = Gamma_(r - 1) (psi(e_r))$ are zero by induction, hence so is that of $Gamma_r (G)$, and $psi((E_r)_(m_i)) = 0$.
  For the fourth, suppose that $psi(e_l)[v] = 0$ for every $l <= r$.
  By induction $G'[v] = psi(pi) G[v]$ and $psi(E)[v] = psi(pi) psi(e_r)[v] = 0$, so that $Gamma_r (G)[v] = psi(E_m) G'[v] slash psi(pi) = psi(E_m) G[v]$.
  For the fifth, both conditions include, by induction, that $psi(e_l)[v] = 0$ for every $l < r$; under this condition the fourth statement for the chain $epsilon_1, dots, epsilon_(r - 1)$ gives $psi(E)[v] = psi(pi) psi(e_r)[v]$, and $psi(pi) != 0$.
  For the last, if $m_l = m_i$ with $l < i$, the third statement gives $psi((E_i)_(m_i)) = psi((E_i)_(m_l)) = 0$.
]

The first two statements say that the recorded equations are obtained from the originals by a lower triangular matrix, and the third that they are upper triangular in the eliminated unknowns.
Comparing determinants identifies the pivots, as in Bareiss elimination @bareiss1968.

#proposition[
  Let $epsilon_1, dots, epsilon_r$, with $epsilon_i = (E_i, m_i, pi_(i - 1))$, be an elimination chain over $psi$ with originals $e_1, dots, e_r$ and current pivot $pi_r$.
  Then $psi(pi_r)$ is the determinant of the square matrix of size $r$ with entries $psi((e_i)_(m_l))$, for $1 <= i, l <= r$.
  If moreover $m_1, dots, m_r$ are pairwise distinct and smaller than $r$, then
  $ psi(pi_r) = plus.minus det (psi((e_i)_j))_(1 <= i <= r, thin 0 <= j < r). $
] <prop:minor>

#proof[
  Let $A$ and $B$ be the square matrices of size $r$ with entries $A_(i l) := psi((e_i)_(m_l))$ and $B_(i l) := psi((E_i)_(m_l))$.
  By the second statement of @prop:chain, $B = T A$ for a lower triangular matrix $T$ with diagonal entries $psi(pi_0), dots, psi(pi_(r - 1))$.
  By the third, $B$ is upper triangular, and its diagonal entries are $psi((E_i)_(m_i)) = psi(pi_i)$ for $i = 1, dots, r$.
  Taking determinants,
  $ psi(pi_1) dots.c psi(pi_r) = psi(pi_0) dots.c psi(pi_(r - 1)) det A. $
  Since $pi_0 = 1$, both sides contain the factor $psi(pi_0) dots.c psi(pi_(r - 1))$, which is not zero by the definition of a chain, and $psi(pi_r) = det A$.
  Under the additional hypothesis, $l |-> m_l$ is a bijection from ${1, dots, r}$ onto ${0, dots, r - 1}$, and $A$ is the matrix $(psi((e_i)_j))$ with its columns permuted accordingly, so that the two determinants differ by the sign of a permutation.
]

On a complete record every unknown but the scale is eliminated, and the scale coefficient of the final equation acts as one more pivot.
It is the polynomial whose roots are the candidate proportions.

#proposition[
  Let $rho$ be a complete admissible record with $k$ inside placements, and consider a successful pass along $rho$, from the initial stage for integers $a$ and $b$, with final equation $E_"fin"$.
  Let $e_1, dots, e_(k + 1)$ be the equations of the homogeneous system of $rho$, and let $M$ be the square matrix of size $k + 1$ over $R$ with entries $(e_i)_j$, for $1 <= i <= k + 1$ and $0 <= j <= k$.
  Then the pass records $k$ eliminations, and
  $ (E_"fin")_0 = plus.minus det M. $
  Consequently, if $chi$ is a homomorphism from $R$ to the real numbers and $w in RR^(k + 1)$ satisfies $w_0 = 1$ and $e_i [w] = 0$ for every $i$, then $chi((E_"fin")_0) = 0$.
] <prop:det>

#proof[
  Let $psi$ be the inclusion of $R$ in its field of fractions.
  The pivots $(E_i)_(m_i)$ of the recorded eliminations are not zero, by the definition of a pass, so @prop:trace applies.
  The homogeneous system has $k + 1$ equations by @prop:count, since the rules are independent of the arithmetic of lengths; hence the recorded eliminations are $k$ in number, they form a chain with originals $e_1, dots, e_k$ and current pivot $pi_k != 0$, and $psi(E_"fin") = Gamma_k (psi(e_(k + 1)))$.
  The triple $(E_"fin", 0, pi_k)$, with the original $e_(k + 1)$, therefore extends the chain to one of length $k + 1$ with current pivot $(E_"fin")_0$.
  The indices $m_1, dots, m_k$ lie between $1$ and $k$, by the definition of a pass, and are pairwise distinct, by the last statement of @prop:chain; with the index $0$ they are $k + 1$ distinct indices smaller than $k + 1$.
  By @prop:minor, $psi((E_"fin")_0) = plus.minus det psi(M)$, and $psi$ is injective.
  For the consequence, the real matrix $chi(M)$ sends the vector $w != 0$ to zero, so that $chi(det M) = det chi(M) = 0$.
]

The consequence holds whether or not a pivot vanishes at the point considered: every solution of the system is among the roots of the final coefficient.
The same argument, with a floor or a wall appended as one more equation, shows that the divisions of the pass are exact.

#proposition[
  Let $(S, pi, k)$ be a stage obtained from the initial stage for integers $a$ and $b$ by finitely many steps, each of which leads from a stage to the stage that the second or the third clause of @def:elimination defines for some placement at one of its tiers.
  Let $p$ be a placement at a tier of $S$ that has an equation $E$ on $S$, and let $S^+$ be the staircase obtained by placing $p$ on $S$ with free side $pi u_(k + 1)$.
  Then, for every index $m$ with $E_m != 0$, the elimination $(E, m, pi)$ divides exactly every floor and wall of $S^+$.
] <prop:exact>

#proof[
  Let $psi$ be the inclusion of $R$ in its field of fractions $K$.
  The stage has the properties established in the proof of @prop:trace, whose induction applies to the steps considered here, because the pivots are non-zero elements of $R$ and $psi$ is injective: there is a chain $epsilon_1, dots, epsilon_r$ over $psi$, with originals $e_1, dots, e_r$ and current pivot $pi$, such that $psi(E) = Gamma_r (psi(e))$ and $psi(F) = Gamma_r (psi(hat(F)))$ for every floor or wall $F$ of $S^+$, where $e$ and $hat(F)$ are forms over $R$.
  Let $epsilon := (E, m, pi)$, which extends the chain, with the original $e$, to one with current pivot $E_m != 0$, and let $G := gamma_epsilon (psi(F))$, so that
  $ G_j = psi(E_m F_j - F_m E_j) / psi(pi) quad "and" quad G = Gamma_(r + 1) (psi(hat(F))). $
  Fix an index $j$.
  The images under $psi$ of the forms $E_1, dots, E_r, E$ and of the originals form an elimination chain over the identity of $K$, and the triple $(G, j, psi(E_m))$, with the original $psi(hat(F))$, extends it to a chain of length $r + 2$ with current pivot $G_j$.
  By the first statement of @prop:minor, $G_j$ is the determinant of a matrix whose entries are images under $psi$ of coefficients of $e_1, dots, e_r$, $e$ and $hat(F)$, hence $G_j = psi(Delta)$ for some $Delta in R$.
  Then $psi(E_m F_j - F_m E_j) = psi(pi Delta)$, and $pi$ divides $E_m F_j - F_m E_j$ because $psi$ is injective.
]

The final coefficient is, up to trivial factors, the polynomial $F_rho$ of the direct method.

#proposition[
  Let $rho$ be a complete admissible record with $k$ inside placements, let $a$ and $b$ be integers, and consider a successful pass along $rho$ over $R = ZZ[x, x^(-1)]$, from the initial stage for $a$ and $b$, with final equation $E_"fin"$.
  Suppose that the elimination of the direct method succeeds on $rho$, with the notation of @def:reference.
  Then there are $lambda in ZZ[x]$ and an integer $e$ such that $D = lambda det A$ and
  $ lambda (E_"fin")_0 = plus.minus x^e F_rho. $
] <prop:target>

#proof[
  Let $lambda$ be given by the specification of the elimination, so that $D = lambda det A$ and $N_(k + 1) = lambda det A_(k + 1)$.
  To a linear form $f = (d, c)$ of @def:forms assign the form $tau(f)$ over $R$ with coefficients
  $ tau(f)_0 := x^(-d) (a c_1 + b c_0), quad tau(f)_j := x^(-d) c_(j + 1) quad "for" j >= 1, $
  which expresses the substitution of $a t$ for $W$ and of $b t$ for $1$.
  A direct verification on the four operations shows that $tau$ is a homomorphism, and it sends the forms $W$, $1$ and $s_j$ to $a u_0$, $b u_0$ and $u_j$.
  Since placing commutes with homomorphisms, the equations of the homogeneous system are $e_i = tau(g_i)$.
  Hence the matrix $M$ of @prop:det has the entries $M_(i 0) = x^(-d_i) (a A_(i, k + 1) - b c_i)$ and $M_(i j) = x^(-d_i) A_(i j)$ for $1 <= j <= k$: it is obtained from $A$ by replacing the last column by $a$ times itself minus $b$ times the vector $c$, moving that column to the first place, and multiplying the $i$-th row by $x^(-d_i)$.
  Since the determinant is linear in the last column,
  $ det M = plus.minus x^e (a det A - b det A_(k + 1)), quad e := -sum_i d_i, $
  and multiplying by $lambda$ gives $lambda det M = plus.minus x^e (a D - b N_(k + 1)) = minus.plus x^e F_rho$.
  The statement follows from @prop:det.
]

For Bareiss elimination, $lambda = plus.minus 1$, and the two polynomials have the same roots in $[1, infinity)$; in general the statement shows that every root of the final coefficient in $[1, infinity)$ is a root of $F_rho$, and that every root of $F_rho$ at which $lambda$ does not vanish is a root of the final coefficient.
The correctness of the incremental search does not depend on this comparison, which is stated for completeness.

The cost of an elimination is proportional to the square of the number of tiers, and most nodes of the search tree are close to the leaves, where staircases have one or two tiers.
In the implementation, when one tile remains to be placed, on a single tier that is not stale and whose floor and wall are non-zero multiples $c_L t$ and $c_M t$ of the scale, and no forced placement is pending, the final equations $c_L - x c_M$ and $c_M - x c_L$ of the two orientations of the last tile are formed directly, without a separate placement.

Away from the zeros of the pivots, the recorded eliminations determine the solution of the system.

#proposition[
  Let $rho$ be a complete admissible record with $k$ inside placements and $n$ placements in all, and consider a successful pass along $rho$, with recorded eliminations $epsilon_1, dots, epsilon_k$, where $epsilon_i = (E_i, m_i, pi_(i - 1))$, final equation $E_"fin"$ and recorded sizes $sigma_1, dots, sigma_n$.
  Let $chi$ be a homomorphism from $R$ to the real numbers such that $chi((E_i)_(m_i)) != 0$ for every $i$.
  Let $v in RR^(k + 1)$ be obtained from $(1, 0, dots, 0)$ by replacing, for $i = k, k - 1, dots, 1$ in turn, the coordinate $v_(m_i)$ by
  $ -1 / chi((E_i)_(m_i)) sum_(j <= k, thin j != m_i) chi((E_i)_j) v_j. $
  + $v_0 = 1$.
  + If $chi((E_"fin")_j) = 0$ for every $j >= 1$, then $e_i [v] = 0$ for every $i <= k + 1$ if and only if $chi((E_"fin")_0) = 0$.
  + If $w in RR^(k + 1)$ satisfies $w_0 = 1$ and $e_i [w] = 0$ for every $i <= k + 1$, then $w = v$.
  + There is $pi in R$ with $chi(pi) != 0$ such that, for every $q <= n$, the form $chi(sigma_q)$ carried through the eliminations recorded with $p_q$ and with the later placements, in order, has the value $chi(pi) kappa_q [v]$ at $v$.
] <prop:back>

#proof[
  By @prop:trace with $psi = chi$, and by the count in @prop:det, the eliminations form a chain over $chi$ with originals $e_1, dots, e_k$, the current pivot $pi := pi_k$ satisfies $chi(pi) != 0$, and $chi(E_"fin") = Gamma_k (chi(e_(k + 1)))$.
  By @prop:chain and the definition of a pass, $m_1, dots, m_k$ are pairwise distinct and lie between $1$ and $k$, so they are all the indices from $1$ to $k$, and $chi((E_i)_(m_l)) = 0$ for $l < i$.
  In particular no replacement changes $v_0$, which proves the first statement.

  When $v_(m_i)$ is replaced, the equation $chi(E_i)[v] = 0$ becomes true; the later replacements change only the coordinates $v_(m_l)$ with $l < i$, whose coefficients in $E_i$ have image zero, so the equation still holds at the end.
  Hence $chi(E_i)[v] = 0$ for every $i <= k$, and $e_i [v] = 0$ for every $i <= k$ by the fifth statement of @prop:chain.
  The fourth statement of @prop:chain then gives $chi(E_"fin")[v] = Gamma_k (chi(e_(k + 1)))[v] = chi(pi) e_(k + 1) [v]$.
  Under the hypothesis of the second statement, $chi(E_"fin")[v] = chi((E_"fin")_0) v_0 = chi((E_"fin")_0)$, and the statement follows because $chi(pi) != 0$.

  For the third statement, $chi(E_i)[w] = 0$ for every $i <= k$, by the fifth statement of @prop:chain.
  We show that $w_(m_i) = v_(m_i)$ by descending induction on $i$.
  In the equation $chi(E_i)[w] = 0$ the coefficients of the unknowns of index $m_l$ with $l < i$ are zero; the other unknowns are that of index $0$, with $w_0 = v_0$, those of index $m_l$ with $l > i$, with $w_(m_l) = v_(m_l)$ by induction, and that of index $m_i$, whose coefficient is not zero.
  Hence $w_(m_i)$ is given by the same expression as $v_(m_i)$, whose value was computed from coordinates that did not change afterwards.

  For the fourth, $chi(sigma_q) = Gamma_(r(q)) (chi(kappa_q))$ by @prop:trace, so that carrying it through the eliminations $epsilon_(r(q) + 1), dots, epsilon_k$ gives $Gamma_k (chi(kappa_q))$, whose value at $v$ is $chi(pi) kappa_q [v]$ by the fourth statement of @prop:chain.
]

== Candidate roots <sec:candidates>

At the end of a successful pass along a complete record, the method examines the final equation.
If its scale coefficient $c := (E_"fin")_0$ is not zero and its other coefficients are zero, the candidates for the proportion are the roots of $c$ in $[1, infinity)$, by @prop:det.
The Laurent polynomial $c$ is normalised to a polynomial $"key"(c) in ZZ[x]$, which differs from it by a sign and a power of $x$.
A polynomial whose expansion in powers of $x - 1$ has non-negative coefficients and positive constant term has no root in $[1, infinity)$, by @prop:noroot, and is discarded.
The roots of the others are obtained from a table shared by all threads, indexed by the coefficients, so that each polynomial is factorised once; this is the routine of @def:primitives that the direct method uses.
Different records often lead to the same polynomial: for a square and thirteen tiles, $2.8 times 10^11$ records lead to $2.6 times 10^8$ polynomials with a root in $[1, infinity)$.

== Numerical verification <sec:numeric>

Let $r$ be a candidate root, known through an enclosing interval of floating-point numbers of relative width about $10^(-15)$.
The tile sizes at $r$ are computed in interval arithmetic with outward rounding: the eliminations along the path are undone in reverse order, each giving the eliminated unknown as a quotient of interval values, and the placements are then replayed on intervals.
As for the exact routines, the interval arithmetic is not part of what is proved, and enters through its specifications.

#definition(name: [numerical routines])[
  The _numerical routines_ operate on a set of _intervals_, each of which _encloses_ certain real numbers, and are the following, with their assumed specifications.
  + _Arithmetic._ Every integer $z$ has an interval $[z]$ that encloses it.
    There are a sum, a difference, a product and a negation of intervals; if $I$ encloses $alpha$ and $J$ encloses $beta$, then $I + J$, $I - J$, $I J$ and $-I$ enclose $alpha + beta$, $alpha - beta$, $alpha beta$ and $-alpha$.
    There is a quotient of intervals; if $I$ encloses $alpha$, $J$ encloses $beta$ and $J$ is certainly away from zero, then $I slash J$ encloses $alpha slash beta$.
  + _Decisions._ An interval may be found _certainly away from zero_, _certainly not positive_ or _certainly positive_; every number that it encloses is then different from zero, not positive, or positive, respectively.
  + _Enclosure of polynomials._ Given $c in ZZ[x, x^(-1)]$ and an interval $I$, the routine either fails or returns an interval $c(I)$.
    In the second case, if $I$ is certainly away from zero, then $c(I)$ encloses $c(alpha)$ for every $alpha > 0$ that $I$ encloses.
  + _Roots._ Every real number $r$ has a stored interval $I_r$.
    If $r >= 1$ and $q(r) = 0$ for some non-zero $q in ZZ[x]$, then $I_r$ encloses $r$ and is certainly away from zero.
  + _Minimal polynomials._ A real number $r$ may have a stored polynomial $mu_r in ZZ[x]$, and then $mu_r (r) = 0$.
    There is a divisibility test for pairs of polynomials of $ZZ[x]$; if it succeeds for $(f, q)$, then $f$ divides $q$ in $ZZ[x]$.
  + _Coefficients._ For every $c in ZZ[x, x^(-1)]$ there are polynomials $"key"(c)$ and $"coeffs"(c)$ in $ZZ[x]$ and integers $e$ and $e'$ such that $"key"(c) = plus.minus x^e c$ and $"coeffs"(c) = x^(e') c$.
] <def:numerics>

Nothing is assumed of a divisibility test that does not succeed, nor is the stored polynomial assumed to be irreducible.
The intervals form an arithmetic of lengths for a given interval $I$ of the proportion, in which the product and the quotient by $x$ are the product and the quotient by $I$.

#definition(name: [numerical check])[
  Let $rho$ be a complete admissible record with $k$ inside placements and $n$ placements, with a successful pass over $ZZ[x, x^(-1)]$ from the initial stage for $a$ and $b$, with recorded eliminations $epsilon_1, dots, epsilon_k$, where $epsilon_i = (E_i, m_i, pi_(i - 1))$, and recorded sizes $sigma_1, dots, sigma_n$; and let $r$ be a real number, with stored interval $I := I_r$.
  The _numerical check_ of $r$ returns a verdict, which is _accept_, _reject_ or _unsure_, as follows.
  + _Back-substitution._ Let $V_0 := [1]$ and $V_j := [0]$ for $1 <= j <= k$.
    For $i = k, k - 1, dots, 1$ in turn, the enclosures $(E_i)_j (I)$ are computed for $j = m_i$ and for the indices $j <= k$ other than $m_i$ with $(E_i)_j != 0$; then $V_(m_i)$ is replaced by the quotient by $(E_i)_(m_i) (I)$ of the negation of the sum of the products $(E_i)_j (I) V_j$ over the latter indices, the sum starting from $[0]$.
    If an enclosure fails, or if some $(E_i)_(m_i) (I)$ is not certainly away from zero, the verdict is unsure.
  + _Replay._ The record $rho$ is placed on the initial staircase of intervals with floor $[a]$ and wall $[b]$, with free sides $V_1, dots, V_k$ and with $I$ as the interval of the proportion; let $P_1, dots, P_n$ be the positive quantities of its placements.
  + _Decision._ If some $P_q$ is certainly not positive, the verdict is reject.
    Otherwise, if every $P_q$ is certainly positive, the verdict is accept.
    Otherwise the placements $q$ for which $P_q$ is not certainly positive are examined in order, as follows, and the verdict is reject if one of them yields a _certificate_ and unsure if the examination ends without one.
    The elimination recorded with $p_q$, if any, and those recorded with the later placements are applied in order to $sigma_q$; if one of them does not divide exactly, the examination ends.
    Let $F$ be the resulting form.
    If $F_j != 0$ for some $j >= 1$, the examination ends.
    If $F_0 = 0$, there is a certificate.
    Otherwise, if $r$ has no stored polynomial, the examination ends; if the divisibility test succeeds for $(mu_r, "coeffs"(F_0))$, there is a certificate; and if it does not, the examination passes to the next placement.
] <def:check>

An accepted root is a solution, and a rejected one is not, with or without a certificate.

#proposition[
  Let $rho$ be a complete admissible record, with a successful pass over $ZZ[x, x^(-1)]$ from the initial stage for integers $a$ and $b$, with final equation $E_"fin"$, and let $alpha > 0$ be a real number whose stored interval encloses $alpha$ and is certainly away from zero.
  + If $(E_"fin")_j = 0$ for every $j >= 1$, if $(E_"fin")_0 (alpha) = 0$, and if the verdict of the numerical check of $alpha$ is accept, then there is $s$ such that $(a, b, s)$ satisfy the constraints of $rho$ at $alpha$.
  + If the verdict is reject, there is no $s$ such that $(a, b, s)$ satisfy the constraints of $rho$ at $alpha$.
] <prop:numeric>

#proof[
  Let $chi$ be the evaluation of Laurent polynomials at $alpha$.
  In both cases the verdict is not unsure, so the back-substitution on intervals has succeeded.
  For each $i$, the interval $(E_i)_(m_i) (I)$ encloses $chi((E_i)_(m_i))$ and is certainly away from zero, so that $chi((E_i)_(m_i)) != 0$, and @prop:back applies; let $v$ be the vector defined there.
  The interval $V_j$ encloses $v_j$ at every step of the two back-substitutions, carried out in parallel: this holds at the start, and each replacement preserves it by the specifications of the arithmetic and of the enclosures; the terms omitted from the sum of intervals are those whose coefficient is zero.

  The pairs $(xi, J)$ of a real number and an interval that encloses it form an arithmetic of lengths, with the operations of the real numbers for the proportion $alpha$ on the first component and those of the intervals for the interval $I$ on the second; the specifications say that these operations lead from pairs to pairs; the quotient by $I$ is allowed because $I$ is certainly away from zero.
  The two projections are homomorphisms.
  Placing $rho$ on the initial staircase with floor $(a, [a])$ and wall $(b, [b])$, with free sides $(v_j, V_j)$, therefore shows that each $P_q$ encloses the corresponding positivity constraint of $rho$ for $(a, b, (v_1, dots, v_k))$ at $alpha$, which is $kappa_q [v]$ by the proof of @prop:hom.

  For the first statement, the second statement of @prop:back shows that $e_i [v] = 0$ for every $i$, and $kappa_q [v] > 0$ for every $q$ because every $P_q$ is certainly positive.
  By @prop:hom, $(a, b, (v_1, dots, v_k))$ satisfy the constraints of $rho$ at $alpha$.

  For the second statement, suppose that $(a, b, s)$ satisfy the constraints of $rho$ at $alpha$, and let $w := (1, s_1, dots, s_k)$.
  By @prop:hom, $e_i [w] = 0$ for every $i$ and $kappa_q [w] > 0$ for every $q$, and $w = v$ by the third statement of @prop:back.
  Hence $kappa_q [v] > 0$ for every $q$, and no $P_q$ is certainly not positive.
  Since the verdict is reject, there is a certificate for some placement $p_q$: a form $F$ over $ZZ[x, x^(-1)]$, obtained from $sigma_q$ by exact eliminations, with $F_j = 0$ for $j >= 1$, and such that $F_0 = 0$ or $mu_alpha$ divides $"coeffs"(F_0)$.
  In the second case $"coeffs"(F_0)$ vanishes at $alpha$, because $mu_alpha$ does, and it equals $F_0$ multiplied by a power of $x$, with $alpha != 0$; so $F_0 (alpha) = 0$ in both cases.
  The previous pivots of the eliminations are $1$ and the pivots $(E_i)_(m_i)$, whose values at $alpha$ are not zero, so each exact elimination agrees with the corresponding map $gamma$ after evaluation, and $chi(F)$ is $chi(sigma_q)$ carried through the eliminations recorded with $p_q$ and with the later placements.
  By the fourth statement of @prop:back, $chi(F)[v] = chi(pi) kappa_q [v]$ with $chi(pi) != 0$, while $chi(F)[v] = F_0 (alpha) v_0 = 0$.
  Hence $kappa_q [v] = 0$, a contradiction.
]

The case in which the interval for some tile size contains zero arises almost always because the size is exactly zero: the solution is then a tiling with fewer tiles, as for the pinwheel arrangement of five tiles of @fig:pinwheel, whose central tile degenerates to a point.
Such cases are about one in a hundred, and the certificate decides them without recourse to the direct method.
The rejection that it justifies uses only the facts that the stored polynomial vanishes at the root and that a successful divisibility test is correct.
When the stored polynomial is the minimal polynomial of the root, the certificate is moreover complete, by the following statement, which is not used in the correctness of the search.

#proposition[
  Let $f in ZZ[x]$ be primitive and irreducible over $QQ$, and let $r$ be a real number with $f(r) = 0$.
  Then, for every $q in ZZ[x]$, the polynomial $f$ divides $q$ in $ZZ[x]$ if and only if $q(r) = 0$.
] <prop:degenerate>

#proof[
  If $f$ divides $q$ then $q(r) = 0$.
  Conversely, suppose that $q(r) = 0$, and let $mu$ be the minimal polynomial of $r$ over $QQ$, which divides $f$ and $q$ in $QQ[x]$ and is not constant.
  Since $f$ is irreducible, $f$ is the product of $mu$ and a non-zero rational number, and so divides $q$ in $QQ[x]$.
  Since $f$ is primitive, it then divides $q$ in $ZZ[x]$, by Gauss's lemma.
]

With the notation of @def:check, when the form $F$ is obtained and involves the scale only, the positive quantity of $p_q$ is zero in the solution $v$ of @prop:back at the root $r$ exactly if $F_0 (r) = 0$, by the fourth statement of that proposition, hence exactly if the minimal polynomial of $r$ divides $"coeffs"(F_0)$.
The formal development does not prove that the exact eliminations applied to $sigma_q$ always divide exactly, nor that the resulting form involves the scale only; in either case the check returns the verdict unsure.

#definition(name: [incremental method])[
  Let $a$ and $b$ be integers.
  The _incremental method_ treats a complete admissible record $rho$ as follows.
  + It carries out the symbolic pass along $rho$ over $ZZ[x, x^(-1)]$, from the initial stage for $a$ and $b$.
    If the pass fails, $rho$ is _passed to the direct method_.
  + Otherwise, with $E_"fin"$ the final equation, if $(E_"fin")_0 = 0$ or $(E_"fin")_j != 0$ for some $j >= 1$, the record is passed to the direct method.
  + Otherwise let $q := "key"((E_"fin")_0)$.
    If the coefficients of $q(x + 1)$ are non-negative and its constant coefficient is positive, the method reports no proportion.
  + Otherwise it performs the numerical check of every $r in "roots"(q)$.
    If some verdict is unsure, the record is passed to the direct method; otherwise the method reports the numbers $r$ whose verdict is accept.
  For a record passed to the direct method, the incremental method reports the set $"Ref"_(a, b) (rho)$.
  We write $"Fast"_(a, b) (rho)$ for the finite set of numbers reported.
] <def:fastsolve>

For ten tiles, one record in ten thousand is passed to the direct method.
Whenever the incremental method decides a record itself, it reports exactly the solutions of its system, unconditionally.

#proposition[
  Let $a$ and $b >= 1$ be integers and let $rho$ be a complete admissible record.
  A _solution_ of $rho$ is a real number $r >= 1$ for which there is $s$ such that $(a slash b, 1, s)$ satisfy the constraints of $rho$ at $r$.
  + If $rho$ is not passed to the direct method, $"Fast"_(a, b) (rho)$ is the set of solutions of $rho$.
  + Every element of $"Fast"_(a, b) (rho)$ is a solution of $rho$.
  + If $rho$ is not passed to the direct method, or if it is regular for $(a, b)$, every solution of $rho$ belongs to $"Fast"_(a, b) (rho)$.
  + $"Ref"_(a, b) (rho) subset.eq "Fast"_(a, b) (rho)$, with equality if $rho$ is regular for $(a, b)$.
] <prop:fastsolve>

#proof[
  Suppose that $rho$ is not passed to the direct method.
  Then the pass is successful, $c := (E_"fin")_0$ is not zero, the other coefficients of $E_"fin"$ are zero, and $q = "key"(c)$ is a non-zero polynomial with the same zeros as $c$ among the non-zero real numbers.
  Let $r$ be a solution of $rho$.
  By @prop:hom there is $w in RR^(k + 1)$ with $w_0 = 1$ at which the homogeneous system holds for the evaluation at $r$, so $c(r) = 0$ by @prop:det, and $r in "roots"(q)$.
  In particular the third step does not apply if $rho$ has a solution, by @prop:noroot, so that the first statement holds when it applies.
  Suppose that the fourth step applies, and let $r in "roots"(q)$, so that $r >= 1$, $c(r) = 0$, and the stored interval of $r$ encloses $r$ and is certainly away from zero.
  If the verdict for $r$ is accept, $r$ is a solution by @prop:numeric and @prop:hom.
  If $r$ is a solution, its verdict is not unsure, since $rho$ is not passed to the direct method, and it is not reject, by @prop:numeric and @prop:hom; so it is accept.
  This proves the first statement.

  The other statements follow from the first and from @prop:solve.
  If $rho$ is passed to the direct method, $"Fast"_(a, b) (rho) = "Ref"_(a, b) (rho)$ consists of solutions, and contains every solution if $rho$ is regular.
  If it is not, $"Fast"_(a, b) (rho)$ is the set of all solutions, which contains $"Ref"_(a, b) (rho)$, and equals it if $rho$ is regular.
]

== The search <sec:tree>

It remains to relate the depth-first search, which never forms the list of records, to the treatment of the records one at a time.
The search is split into tasks by the first few placements, and a failure of the symbolic pass passes a whole subtree to the direct method.

#definition(name: [enumeration])[
  Fix a truth value, _square_.
  For a bare staircase $S$, an integer $r >= 0$ and a truth value _first_, let $"moves"(S, r, "first")$ be the set of placements that are admissible at $S$ with $r$ tiles remaining, excluding the tall ones when both _square_ and _first_ hold.
  The set $cal(C)(r, "first", S)$ of the _completions_ of $S$ consists of the empty record alone if $S$ is empty; it is empty if $S$ is not empty and $r = 0$; and otherwise it consists of the records formed by a placement $p in "moves"(S, r, "first")$ followed by a record of $cal(C)(r - 1, "false", S')$, where $S'$ is the staircase after $p$.
  For an integer $d >= 0$, the set $cal(P)_d (r, "first", S)$ of the _prefixes_ consists of the empty record alone if $d = 0$ or $S$ is empty, and otherwise of the records formed by a placement $p in "moves"(S, r, "first")$ followed by a record of $cal(P)_(d - 1) (r - 1, "false", S')$.
] <def:enumeration>

The completions are the records of @def:record, and the prefixes cut them at a given depth.

#proposition[
  + A record $(p_1, dots, p_ell)$ belongs to $cal(C)(r, "first", S)$ if and only if each $p_j$ is admissible, with $r - j + 1$ tiles remaining, at the staircase on which it is placed when the record is placed on $S$, the staircase left by the last one is empty, and the first tile is wide if both _square_ and _first_ hold.
    In particular, for the bare initial staircase $S_0$, the set $cal(C)(n, "true", S_0)$ consists of the complete admissible records for $n$ tiles, with the first tile wide if _square_ holds.
  + For every $d >= 0$, a record belongs to $cal(C)(r, "first", S)$ if and only if it consists of a record $rho_1 in cal(P)_d (r, "first", S)$ followed by a record of $cal(C)(r - ell_1, "first"_1, S_1)$, where $ell_1$ is the length of $rho_1$, $S_1$ is the staircase after $rho_1$, and $"first"_1$ holds exactly if _first_ holds and $rho_1$ is empty.
] <prop:enumeration>

#proof[
  The first statement is proved by induction on $r$.
  If $S$ is empty, the only completion is the empty record, and it is the only record that satisfies the condition, since no placement is admissible at the empty staircase.
  If $S$ is not empty and $r = 0$, there is no completion, and no record satisfies the condition: the empty one does not leave an empty staircase, and no placement is admissible with no tile remaining.
  If $S$ is not empty and $r >= 1$, a record satisfies the condition exactly if it is not empty, its first placement belongs to $"moves"(S, r, "first")$, and the rest satisfies the condition for $r - 1$, the staircase $S'$ and _first_ false, that is, belongs to $cal(C)(r - 1, "false", S')$ by induction.

  The second statement is proved by induction on $d$.
  For $d = 0$, and when $S$ is empty, the only prefix is the empty record and the statement is trivial.
  Let $d >= 1$ and $S$ not empty.
  If $r = 0$ there are neither completions nor prefixes.
  If $r >= 1$, a completion is a placement $p in "moves"(S, r, "first")$ followed by a record of $cal(C)(r - 1, "false", S')$, which by induction is a record $rho'_1 in cal(P)_(d - 1) (r - 1, "false", S')$ followed by a completion of the staircase after it, with $r - 1$ diminished by the length of $rho'_1$ and with _first_ false; and the records formed by $p$ followed by such $rho'_1$ are the prefixes in $cal(P)_d (r, "first", S)$.
]

#definition(name: [incremental search])[
  Let $a$ and $b$ be integers, and let _square_ hold exactly if $a = b$.
  Let $Sigma = (S, pi, k)$ be a stage whose staircase is not empty, reached by the symbolic pass along a record $delta$, and let $r >= 0$.
  The search _below_ $Sigma$ with $r$ tiles remaining considers every placement $p$ in $"moves"(overline(S), r, "first")$, where $overline(S)$ is the bare staircase underlying $S$ and _first_ holds exactly if $delta$ is empty, and treats it as the symbolic pass does.
  + If the pass fails at $p$, the search reports $"Ref"_(a, b) (delta p rho')$ for every $rho' in cal(C)(r - 1, "false", S')$, where $S'$ is the bare staircase after $p$.
  + If $p$ has an equation $E$ and empties the staircase, the search treats the record $delta p$ by the second, third and fourth steps of @def:fastsolve, with $E$ as the final equation, and reports accordingly.
  + Otherwise it continues below the next stage of the pass, reached along $delta p$, with $r - 1$ tiles remaining.
  The search with a _forced_ record $rho_1 = (f_1, dots, f_d)$, from the initial stage with $n$ tiles remaining, treats $f_1, dots, f_d$ in turn in the same three ways, each only if it belongs to the set of moves at the stage reached, and reports nothing otherwise; in the first case, at a forced placement $f_j$, it reports only for those completions $rho'$ that begin with the remaining forced placements $f_(j + 1), dots, f_d$, or that are complete before these are exhausted and form a beginning of them; in the third case it passes to the next forced placement, and after the last one it continues with the search below the stage reached.
  For integers $d, n >= 0$, the _incremental search_ for $n$ tiles, split at depth $d$, reports the numbers found with $rho_1$ forced, for every $rho_1 in cal(P)_d (n, "true", S_0)$.
] <def:explore>

In the implementation the prefixes are the tasks distributed to the threads.

The search reports what the incremental method reports for the records taken one at a time.

#proposition[
  Let $a$ and $b$ be integers.
  For all $d, n >= 0$, the numbers reported by the incremental search for $n$ tiles, split at depth $d$, are those of
  $ "Fast"_n (a, b) := union.big_rho "Fast"_(a, b) (rho), $
  where $rho$ ranges over the complete admissible records for $n$ tiles, in which moreover the first tile is wide if $a = b$.
] <prop:searched>

#proof[
  For a stage $Sigma$ reached along $delta$ and a record $rho'$, let $B(Sigma, delta, rho')$ be the set that the incremental method reports for the record $delta rho'$ when its symbolic pass, having reached $Sigma$ after $delta$, is continued along $rho'$.
  For the initial stage and the empty $delta$ this is $"Fast"_(a, b) (rho')$.
  The staircase of a stage and the bare staircase obtained by the same placements have the same flags, since an elimination changes only the lengths.

  We show by induction on $r$ that the numbers reported by the search below $Sigma = (S, pi, k)$ with $r$ tiles remaining are those of the sets $B(Sigma, delta, rho')$ for $rho' in cal(C)(r, "first", overline(S))$.
  If $r = 0$ nothing is reported, and there is no completion because $S$ is not empty.
  Let $r >= 1$.
  The completions are the records $p rho''$ with $p in "moves"(overline(S), r, "first")$ and $rho'' in cal(C)(r - 1, "false", S')$.
  If the pass fails at $p$, then $B(Sigma, delta, p rho'') = "Ref"_(a, b) (delta p rho'')$ for every such $rho''$, which is what the search reports.
  If $p$ has an equation and empties the staircase, the only such $rho''$ is the empty record, and $B(Sigma, delta, p)$ is what the search reports.
  Otherwise the next stage $Sigma'$ has a staircase that is not empty, $B(Sigma, delta, p rho'') = B(Sigma', delta p, rho'')$, and the induction hypothesis applies to $Sigma'$.

  The same case distinction, applied to the forced placements in turn, shows two things for the search with $rho_1$ forced: every number that it reports belongs to $B(Sigma_0, nothing, rho')$ for some $rho' in cal(C)(n, "true", S_0)$, with $Sigma_0$ the initial stage; and it reports every number of $B(Sigma_0, nothing, rho_1 rho_2)$ whenever $rho_1 rho_2 in cal(C)(n, "true", S_0)$.
  In the first case of the definition, indeed, the search reports for the completions below the forced placement at which the pass fails that continue with the remaining forced placements, and $rho_2$ preceded by these is one of them.
  By the first statement of @prop:enumeration, the records of $cal(C)(n, "true", S_0)$ are those over which the union is taken, so every number reported belongs to $"Fast"_n (a, b)$.
  Conversely, by the second statement of @prop:enumeration, every such record is of the form $rho_1 rho_2$ with $rho_1 in cal(P)_d (n, "true", S_0)$, so every number of $"Fast"_n (a, b)$ is reported.
]

Restricting the first case, at a forced placement, to the completions that continue with the remaining forced placements ensures that no record is treated under two prefixes: the records examined under the prefixes of the split, taken in order, are exactly the complete admissible records, each once, whether or not the pass fails and wherever it does.
This is proved in the formal development (`examined_split`, `examined_once`).
An earlier version of the implementation reported, in that case, for all the completions below the failing placement, under every prefix through it; the formalisation exposed this, which left the set of numbers reported unchanged but would have counted records more than once, and the implementation was corrected.
No such failure had been observed.

#definition(name: [certified incremental search])[
  Let $a$ and $b$ be integers and $n >= 0$.
  The incremental search for $n$ tiles is _certified_ if every complete admissible record for $n$ tiles, in which moreover the first tile is wide if $a = b$, that the incremental method passes to the direct method is regular for $(a, b)$.
] <def:fastcert>

This is what the two counts of the direct method establish in a run of the incremental search, in which the direct method treats only the records passed to it.

#proposition[
  Let $a, b >= 1$ and $n >= 0$ be integers.
  + $"Fast"_n (a, b) subset.eq P_n (a, b)$.
  + If the incremental search for $n$ tiles is certified, then $"Fast"_n (a, b) = P_n (a, b)$.
  + $"Ref"_n (a, b) subset.eq "Fast"_n (a, b)$; and if the direct search for $n$ tiles is certified, then so is the incremental search, and $"Fast"_n (a, b) = "Ref"_n (a, b)$.
] <prop:fast>

#proof[
  The first two statements are proved as @prop:reference, with @prop:fastsolve in place of @prop:solve.
  An element of $"Fast"_(a, b) (rho)$ is a solution of $rho$, and gives a tiling by @prop:sound and @prop:scaling.
  Conversely, an element of $P_n (a, b) = P_n (a slash b, 1)$ is a solution of a complete admissible record $rho$ for $n$ tiles, with the first tile wide if $a = b$, by @prop:complete and @prop:square; if the search is certified, $rho$ is not passed to the direct method or is regular, and the solution belongs to $"Fast"_(a, b) (rho)$.
  The third statement follows record by record from the last statement of @prop:fastsolve, since a certified direct search is one in which every record considered is regular.
]

The first statement is unconditional: every number that the incremental search reports is the proportion of a tiling.
The two searches can differ only at a record that the incremental method decides itself and that is not regular for the direct method, because a singular situation is counted or the record is flagged as constant; there the incremental method reports every solution and the direct method may report nothing.
No such record is known.
Completeness of the incremental search needs less than that of the direct search, namely the regularity only of the records passed to the direct method.

= Formalisation <app:formal>

The statements of @sec:tilings, @sec:staircases, @sec:systems and @app:solving have been formalised in Lean 4 with Mathlib, in a development distributed with the implementation, in the directory `lean` of its repository.
The development contains no unproved statement and no axiom of its own; its main theorems depend only on the three axioms `propext`, `Classical.choice` and `Quot.sound` of Lean and Mathlib.
@tab:formal lists, for each definition and proposition of those sections, the declarations that formalise it, by module of the namespace `Rectiling`; those of the modules `Elimination`, `BackSubstitution`, `Determinant`, `Reduced`, `Certified`, `Fast`, `Search`, `Exact` and `Target` lie in the namespace `Rectiling.Fast`.
The proofs given in this paper follow those of the development, statement by statement.

#let lean-row(statement, ..declarations) = (statement, declarations.pos().join(linebreak()))

#[
  #show figure.where(kind: table): set block(breakable: true)
  #figure(
    kind: table,
    block(breakable: true, {
      set text(size: 0.82em)
      set par(justify: false)
      show raw: set text(size: 0.8em)
      table(
        columns: (auto, 1fr),
        align: (left + top, left + top),
        table.header([*Statement*], [*Module: declarations*]),
        table.hline(stroke: 0.05em),
        ..lean-row(
          [@def:rectangle],
          [`Geometry`: `Rect`, `Rect.closed`, `Rect.inner`, `Rect.Nondegenerate`, `Rect.HasProportion`],
        ),
        ..lean-row(
          [@def:tiling],
          [`Geometry`: `IsTiling`, `IsSimilarTiling`, `IsTiling.perm`, `IsTiling.eq_of_not_disjoint`, `Rect.separated_of_disjoint`],
        ),
        ..lean-row([@def:counts], [`Persistence`: `TilesWith`]),
        ..lean-row([@prop:scaling], [`Scaling`: `IsSimilarTiling.scale`], [`Persistence`: `TilesWith.scale`]),
        ..lean-row(
          [@prop:transposition],
          [`Geometry`: `IsSimilarTiling.transpose`],
          [`Persistence`: `TilesWith.transpose`, `tilesWith_main_inv`],
        ),
        ..lean-row(
          [@prop:subdivision],
          [`Refinement`: `IsSimilarTiling.refine`],
          [`Persistence`: `Rect.isTiling_four`, `Rect.isTiling_six`, `Rect.isTiling_eight`, `TilesWith.add_three`, `TilesWith.add_five`, `TilesWith.add_seven`, `TilesWith.add_of_five_le`, `persistence`],
        ),
        ..lean-row(
          [@def:staircase],
          [`Staircase`: `Algebra`, `Tier`, `initial`, `realAlgebra`, `unitAlgebra`, `Algebra.IsHom`, `Tier.map`],
        ),
        ..lean-row([@def:region], [`Layout`: `geom`, `GTier.Mem`, `unfilled`, `region`, `Positive`, `region_initial`]),
        ..lean-row(
          [@def:placement],
          [`Staircase`: `Fit`, `Placement`, `tileSize`, `positiveOf`, `equationOf`],
          [`Layout`: `tileAt`],
        ),
        ..lean-row([@def:placing], [`Staircase`: `place`, `length_place`, `place_map`]),
        ..lean-row(
          [@def:admissible],
          [`Staircase`: `Allows`, `Admits`],
        ),
        ..lean-row([@def:record], [`Staircase`: `Allowed`, `CompleteFrom`, `Complete`, `FirstWide`, `allowed_map`]),
        ..lean-row(
          [@prop:bound],
          [`Soundness`: `CompleteFrom.allowed`, `Complete.length`],
          [`Completeness`: `Allowed.completeFrom`],
        ),
        ..lean-row(
          [@def:system],
          [`Staircase`: `positives`, `equations`, `Satisfies`, `run_congr`],
          [`Layout`: `tiles`],
        ),
        ..lean-row(
          [@prop:count],
          [`Staircase`: `length_equations`],
          [`Solver`: `length_symEquations`],
          [`Reduced`: `length_homEquations`],
        ),
        ..lean-row(
          [@obs:strips],
          [`Layout`: `geom_bounds`],
          [`Region`: `stepHyp_of_positive`],
        ),
        ..lean-row(
          [@prop:step],
          [`Layout`: `geom_place`],
          [`Region`: `StepHyp`, `step_region`],
          [`Soundness`: `positive_parts`],
        ),
        ..lean-row([@def:doom], [`Soundness`: `DoomF`, `DoomW`]),
        ..lean-row([@prop:size], [`Soundness`: `size_facts`]),
        ..lean-row([@prop:doom], [`Soundness`: `StepData.doomF`, `StepData.doomW`]),
        ..lean-row([@prop:fit], [`Soundness`: `not_doom`, `StepData.positive_place`]),
        ..lean-row([@prop:sound], [`Soundness`: `tiles_from`, `soundness`]),
        ..lean-row([@def:extends], [`Extension`: `Ext`]),
        ..lean-row(
          [@prop:near],
          [`Extension`: `exists_gap`, `IsTiling.exists_tile_above_right`, `IsTiling.exists_tile_below_right`],
        ),
        ..lean-row([@def:state], [`Extension`: `GInv`, `FlagsOK`], [`Completeness`: `CInv`]),
        ..lean-row([@prop:anchor], [`Extension`: `Around.not_mem`, `GInv.anchor_tile`]),
        ..lean-row(
          [@prop:extension],
          [`Extension`: `GInv.step`, `flagsOK_gpreAfter`, `flagsOK_gmidAfter`, `flagsOK_gpostAfter`],
          [`Completeness`: `exists_first_tier`, `tileSize_of_tile`, `CInv.step`],
        ),
        ..lean-row([@prop:complete], [`Staircase`: `allowed_map`], [`Completeness`: `complete_from`, `completeness`]),
        ..lean-row([@prop:square], [`Completeness`: `head_tile_origin`, `completeness_square`]),
        ..lean-row([@def:mosaic], [not formalised]),
        ..lean-row(
          [@def:forms],
          [`Forms`: `Form`, `formAlgebra`, `Form.num`, `Form.value`, `symInitial`, `symFresh`, `symEquations`, `symPositives`],
        ),
        ..lean-row([@prop:forms], [`Forms`: `formAlgebra_isHom`, `satisfies_iff_forms`]),
        ..lean-row([@def:primitives], [`Solver`: `Primitives`, `Primitives.ideal`]),
        ..lean-row(
          [@def:reference],
          [`Solver`: `systemMatrix`, `systemRhs`, `target`, `numerator`, `NoRootTest`, `Solved`, `solve`],
        ),
        ..lean-row([@prop:noroot], [`Solver`: `NoRootTest.ne_zero`]),
        ..lean-row(
          [@prop:solve],
          [`Solver`: `map_mulVec_cramer`, `map_cramer_of_solution`, `solve_sound`, `solve_complete`, `solve_spec`],
        ),
        ..lean-row([@def:regular], [`Main`: `Reported`, `Certified`]),
        ..lean-row([@prop:reference], [`Main`: `reported_sound`, `reported_complete`, `reported_iff`]),
        ..lean-row(
          [@def:hom],
          [`Elimination`: `Vec`, `unitVec`, `vecAlgebra`],
          [`BackSubstitution`: `dot`],
          [`Reduced`: `homInitial`, `homEquations`, `homPositives`, `val`],
          [`Certified`: `Coeff`, `propX`, `evalL`],
        ),
        ..lean-row([@prop:hom], [`Reduced`: `satisfies_iff_hom`, `satisfies_scale`], [`Fast`: `solvable_iff`]),
        ..lean-row(
          [@def:elimination],
          [`Elimination`: `Stage`, `Stage.side`, `Elim`, `Step`, `Divisible`, `elimForm`, `Run`, `Run.pivots`],
          [`Reduced`: `Stage.init`],
          [`Fast`: `Limits`, `advance`, `run`, `run_spec`],
        ),
        ..lean-row([@def:chain], [`Elimination`: `carryStep`, `carry`, `carry_isHom`, `mapVec_elimForm`, `Elims`]),
        ..lean-row(
          [@prop:trace],
          [`Elimination`: `step_link`, `Trace`, `Run.trace`],
          [`BackSubstitution`: `Trace.elims`, `Trace.size`],
        ),
        ..lean-row(
          [@prop:chain],
          [`Determinant`: `Elims.carry_eq`, `Elims.row`],
          [`BackSubstitution`: `Elims.carry_pivot`, `Elims.pairwise`, `Elims.dot_carry`, `Elims.true_of_stage`, `Elims.stage_of_true`, `nodup_pivots`],
        ),
        ..lean-row([@prop:minor], [`Exact`: `Elims.pivot_eq_det`], [`Determinant`: `Elims.chain`, `Elims.det_eq`]),
        ..lean-row([@prop:det], [`Reduced`: `Run.final_eq_det`, `Run.final_vanishes`]),
        ..lean-row(
          [@prop:exact],
          [`Exact`: `Elims.mapRecords`, `Elims.divisible`, `Stage.Linked`, `Stage.Linked.divisible`, `Reached`, `division_exact`],
        ),
        ..lean-row([@prop:target], [`Target`: `toHom`, `toHom_isHom`, `homEquations_eq`, `Run.final_eq_target`]),
        ..lean-row(
          [@prop:back],
          [`BackSubstitution`: `back`, `back_solves`, `back_unique`, `covers`],
          [`Reduced`: `solutionOf`, `Run.solution`, `Run.prev_ne_zero`],
        ),
        ..lean-row([@def:numerics], [`Certified`: `Numerics`, `Numerics.ideal`]),
        ..lean-row(
          [@def:check],
          [`Certified`: `rowSum`, `backIv`, `Numerics.ivAlgebra`, `carryExact`, `degenerate`, `Verdict`, `check`],
        ),
        ..lean-row(
          [@prop:numeric],
          [`Certified`: `backIv_mem`, `Numerics.encl_positives`, `carryExact_spec`, `degenerate_spec`, `check_accept`, `check_reject`],
        ),
        ..lean-row([@prop:degenerate], [`Certified`: `dvd_iff_evalAt_eq_zero`]),
        ..lean-row([@def:fastsolve], [`Fast`: `FastNoRoot`, `leaf`, `direct`, `fastSolve`, `Delegated`]),
        ..lean-row(
          [@prop:fastsolve],
          [`Fast`: `Solvable`, `leaf_spec`, `direct_spec`, `fastSolve_sound`, `fastSolve_complete`, `solve_subset_fastSolve`, `fastSolve_eq_solve`],
        ),
        ..lean-row([@def:enumeration], [`Enumeration`: `candidates`, `moves`, `completions`, `after`, `prefixes`]),
        ..lean-row(
          [@prop:enumeration],
          [`Enumeration`: `mem_completions`, `mem_completions_initial`, `mem_completions_iff_prefix`],
        ),
        ..lean-row([@def:explore], [`Search`: `explore`, `exploreForced`, `Searched`]),
        ..lean-row(
          [@prop:searched],
          [`Search`: `below`, `fastSolve_eq_below`, `explore_iff`, `exploreForced_sub`, `exploreForced_sup`, `searched_iff`],
        ),
        ..lean-row([@def:fastcert], [`Fast`: `FastReported`, `FastCertified`]),
        ..lean-row(
          [@prop:fast],
          [`Fast`: `fast_sound`, `fast_complete`, `fast_iff`, `reported_imp_fast`, `Certified.fast`, `fast_iff_reported`],
        ),
      )
    }),
    caption: [The definitions and propositions of @sec:tilings, @sec:staircases, @sec:systems and @app:solving, and the Lean declarations that formalise them.],
  ) <tab:formal>
]

== Differences between the statements <sec:differences>

The statements of the paper and those of the development differ in the following respects, none of which affects their content.

- *Rectangles and tilings.* A rectangle of the development is a quadruple of real numbers with no condition on its sides; positivity is a separate predicate, which a tiling requires of its tiles and which the theorems assume of the main rectangle where they need it.
  A tiling is a list of rectangles, and the number of its tiles is the length of the list.
  The development has no notion of the proportion of a rectangle as a number: it states that a rectangle has proportion $x$, as in @def:rectangle, and the remark that follows that definition is not formalised.
- *Sets of proportions.* The development does not define the sets $P_n (W, H)$.
  Its statements are about the existence of a list of $n$ rectangles that is a similar tiling of proportion $x$ of the rectangle with corner at the origin and given sides, which is the membership of $x$ in $P_n (W, H)$.
  @prop:scaling and the first statement of @prop:transposition are formalised as the invariance of tilings under scaling and transposition, from which the equalities of sets follow; the consequence $P_n (w) = P_n (1 slash w)$ is the theorem `tilesWith_main_inv`.
  The three statements of @prop:subdivision are `TilesWith.add_three`, `persistence` and `TilesWith.add_of_five_le`, the first and the last for an arbitrary main rectangle with positive sides; the development states the second for every step of at least three.
- *The main rectangle.* In the statements on the two searches the development takes the main rectangle with integer sides $a$ and $b$, as @prop:reference and @prop:fast do, and the systems are those of the rectangle of sides $a slash b$ and $1$.
  The soundness statements of the development assume only $b > 0$; the positivity of $W$ and $H$ in @prop:sound is established within the formal proof and is not part of the formal statement.
- *Real numbers and algebraic numbers.* A reported proportion is a real number in the development, and the sets reported are finite sets of real numbers.
  The representation of a proportion by its minimal polynomial and an isolating interval belongs to the routines of @def:primitives, which are assumed.
- *Indices.* The development numbers the inside placements, the free sides and the placements from zero, where the paper numbers them from one.
  A linear form of the development has a coefficient for every natural number, with no finiteness condition.
- *Records.* A record is a list of placements, and the free sides are given by a function on the natural numbers.
  In @prop:complete the development states the orientations as a relation between the list of placements and the list of tiles.
- *Proofs by cases.* The three statements of @prop:step are separate statements of the development, on the anchors, on positivity and on the region; the hypotheses that the last one uses are those of @obs:strips, which the development collects in one structure.
  The four statements of @prop:extension are divided in the development between three theorems: the existence of the tier, the fit of the tile together with the new state in terms of anchors, and the placement with its constraints.
  @prop:fit combines two statements of the development.
  The state of @def:state is formalised with the placed and remaining tiles as two lists whose concatenation is a rearrangement of the tiling.
- *Rings.* The statements on elimination chains are formalised over an arbitrary commutative ring with a homomorphism to a field, and @prop:det over an integral domain; the paper assumes an integral domain throughout.
  In the development the quotient of a division that is not exact is defined to be zero, and a successful pass is an inductive predicate that requires every division to be exact.
- *The invariant of the pass.* @prop:trace is formalised for a pass that starts at any stage related to a staircase without eliminations as in its proof, and its three conclusions are derived from one inductive relation between the records of the pass and the homogeneous system.
- *Minors.* The two statements of @prop:minor are proved separately in the development, by the same comparison of determinants; the paper derives the second from the first.
- *Exactness.* @prop:exact is formalised for the stages reached by the model of the method, which are among those of its statement; the lemmas from which it follows hold for all of them.
- *The search.* The sets of @def:enumeration are lists, in the order in which the search tries the placements.
  The numbers found by the search of @def:explore form a predicate, defined by recursion, and the parallel execution is not modelled.
  The development models the search as in @def:explore, including the restriction to the remaining forced placements when the pass fails at a forced placement (`forcedCompletions`), and proves in addition that every complete admissible record is examined under exactly one prefix (`examined_once`).
  The optional restriction of the search to tilings with few tiles in one orientation, which the incremental search does not impose, is not modelled.

== What is not formalised <sec:unformalised>

The formal development is about a model of the method, and the following lies outside it.

- *The implementation.* The Rust code is not verified.
  The model follows it closely, and the differences are listed in the development's documentation; the main ones are that the model gives every inside placement its own unknown, where the code reuses a small number of slots, and that the caches are absent from the model.
- *The arithmetic routines.* The routines of @def:primitives and @def:numerics are assumed to meet their specifications, and every statement about the two searches is quantified over them.
  This covers the fraction-free elimination, factorisation, the isolation of real roots, the determination of signs, the arithmetic of intervals with its rounding, the enclosure of polynomials, the minimal polynomials and the divisibility test.
  Both sets of specifications are shown to be consistent by exhibiting routines that meet them.
- *Failures.* Nothing is assumed and nothing is proved about the occasions on which the symbolic pass fails for reasons of machine arithmetic or for lack of an unknown to eliminate.
  It is not proved that the final equation of a pass involves the scale only, nor that the exact eliminations of the certificate of @def:check divide exactly; the method checks both and passes the record to the direct method, or returns the verdict unsure, when the check fails.
- *Regularity.* It is not proved that every record is regular in the sense of @def:regular.
  The searches count the exceptions, and the completeness statements of @prop:reference and @prop:fast take their absence as a hypothesis.
- *Uniqueness.* It is not proved that a tiling, or a mosaic class, arises from a single record.
  The agreement of the number of records with the Baxter numbers is checked by computation, and within the development for at most seven tiles.
- *Counts and statistics.* The development is about the set of proportions reported.
  Nothing is proved about the number of records that realise a proportion, the number of polynomials, or any other count or statistic of @sec:results.
- *Degrees and minimal polynomials.* The algebraic degree of a proportion and its minimal polynomial are produced by the assumed routines and are not the subject of any formal statement.

#let re = math.op("Re")
#let lft = math.op("left")
#let rgt = math.op("right")
#let rct = math.op("rect")
#let adj = math.op("adj")

= Properties and conjectures <app:structure>

This appendix collects properties of the sets of proportions, with their proofs, and the conjectures that the computations of @sec:results suggest.
The proofs are complete, except that the following classical results are used without proof; each is named where it is used.
Euler's formula for connected plane graphs, the Jordan curve theorem, and the duality between the minimal cuts of a connected plane graph and the cycles of its dual, in its oriented form, are used in @prop:face-potential and @prop:bsst, on which the count for wide rectangles rests.
Kirchhoff's formulas, which express the determinants and the currents of a network as sums over spanning trees, are used in @prop:threshold, for the explicit threshold, and in @ex:improper.
A few remarks rest on computations made with the search described in @sec:solving; they are marked as such, and no proof depends on them.
Nothing in this appendix has been formalised.
@tab:structure collects the counts to which the appendix refers.

#figure(
  kind: table,
  datatable(csv("data/structure.csv")),
  caption: [For $n$ tiles in a square: the number of proportions; the number of those not achievable with fewer tiles; the number achievable by guillotine tilings; the number $E(n)$ of aspect-ratio functions up to inversion; and the number of rational proportions achievable with a single orientation.],
) <tab:structure>

Throughout, an _orientation vector_ for a set $E$ is an element $epsilon$ of ${+1, -1}^E$.
An orientation vector $epsilon$ on the tiles of a similar tiling of proportion $x$ is _an orientation vector of the tiling_ if every tile $T$ is tall for $x$ when $epsilon_T = +1$ and wide for $x$ when $epsilon_T = -1$.
For $x > 1$ there is exactly one, and for $x = 1$ every orientation vector is one, since the tiles are squares.

== Persistence <sec:persistence>

By @prop:subdivision, proportions persist when three tiles, or five or more, are added, and, for the square, also when four are added.
The steps of one and two fail: of the $433926$ proportions with ten tiles, only $59264$ recur with eleven.
Most proportions achievable with $n$ tiles are not achievable with fewer, as @tab:structure shows: for eleven tiles, $3367969$ out of $3446981$.

The step of four can fail when the main rectangle is not a square, as the examples after @prop:subdivision show.
According to the search, for the main rectangle of aspect ratio $2$, of the proportions with $2$, $3$, $4$ and $5$ tiles, $2$ of $2$, $3$ of $8$, $15$ of $29$ and $43$ of $127$ are not achievable with four more tiles.

The same constructions, applied to the tile at a corner, are injective on tilings, and give inequalities for the numbers $t(n)$ of @def:tbc.
They are much weaker than the growth observed in @tab:tbc.

#proposition[
  Let $n >= 1$, and let $s(n)$ be the number of tilings of the unit square by $n$ squares.
  + $t(n + 3) >= t(n)$.
  + $t(n + 4) >= 2 (t(n) - s(n))$.
  + $t(n + 5) >= 4 t(n)$.
  + Every element of $P_n (1)$ is at most $n$, and $a(n + 3) >= a(n) + 1$.
] <prop:steps>

#proof[
  In each of the first three statements we give a map from similar tilings of the unit square with $n$ tiles to similar tilings with more tiles, and show that the tiling is determined by its image.

  For the first, cut the tile at the bottom-left corner into four by its mid-lines.
  In the image the tile at the bottom-left corner, of width $a$ and height $b$, and the tiles with corners $(a, 0)$, $(0, b)$ and $(a, b)$ are the four pieces; their union is the tile that was cut, namely $[0, 2 a] times [0, 2 b]$, and the other tiles are unchanged.

  For the second, let the tiling have proportion $x > 1$; there are $t(n) - s(n)$ such tilings.
  A similar tiling of the unit square of proportion $x > 1$ has at least two tiles, so the construction of the second statement of @prop:subdivision applies and gives a tiling with $n + 4$ tiles, in which the four tiles of the pinwheel are those that contain the corners of the unit square; we take the pinwheel in which the tile at the bottom-left corner is wide.
  The transpose of this tiling is a similar tiling of the same proportion in which the tile at the bottom-left corner is tall, so that the tilings obtained in the two ways are different.
  In either case, removing the four tiles that contain the corners of the square, after transposing if the tile at the bottom-left corner is tall, leaves the scaled copy of the original tiling.

  For the third, there are four dissections of the unit square into one square of side $2 slash 3$ and five of side $1 slash 3$, according to the corner that the large square occupies.
  Replace the tile $[0, A] times [0, B]$ at the bottom-left corner by the image of one of them under the affine map $(u, v) |-> (A u, B v)$; this gives four tilings with $n + 5$ tiles for each tiling with $n$ tiles.
  Let the tile at the bottom-left corner of the image have width $a$ and height $b$.
  If it is the large piece, then $(A, B) = (3 a slash 2, 3 b slash 2)$, and $[a, 3 a slash 2] times [0, b slash 2]$ is a tile of the image.
  If it is a small piece, then $(A, B) = (3 a, 3 b)$, and the tile of the image that contains the points just to the right of $(a, 0)$ is a piece with corner $(a, 0)$ and of width $a$ or $2 a$, so that $[a, 3 a slash 2] times [0, b slash 2]$, which has the same corner, is not a tile.
  The image thus determines which case holds, hence $A$ and $B$; the pieces are the tiles of the image contained in $[0, A] times [0, B]$, which gives the position of the large piece, and the other tiles are unchanged.

  For the fourth, the long side of a tile of proportion $x$ contained in the unit square is at most $1$, so that its area is at most $1 slash x$; the $n$ tiles have total area $1$, hence $n slash x >= 1$.
  By @prop:subdivision, $P_n (1) subset.eq P_(n + 3) (1)$, and $n + 3 in P_(n + 3) (1)$, by cutting the square into $n + 3$ horizontal strips, while $n + 3 in.not P_n (1)$.
]

== Networks <sec:networks>

Brooks, Smith, Stone and Tutte associate an electrical network with a tiling of a rectangle, in which the tiles are resistors @bsst1940 @prasolov2011.
For a similar tiling the resistances are $x$ and $1 slash x$, and the properties of the aspect ratio as a function of $x$ come from letting $x$ be a complex number.
Networks are therefore defined with complex resistances.

#definition(name: [network and flow])[
  A _network_ $frak(N) = (G, s, t)$ consists of a finite connected graph $G$, with set of vertices $V$ and set of edges $E$, possibly with multiple edges but without loops, and of two distinct vertices $s$ and $t$ of $G$, its _poles_.
  Every edge $e$ is given a reference direction, from its _tail_ $e^-$ to its _head_ $e^+$.
  A family of _resistances_ is a function $r : E -> CC without {0}$, and the numbers $y_e := 1 slash r_e$ are the _conductances_.
  For a complex number $I$, a _flow of value $I$_ is a pair of functions $phi : V -> CC$, the _potential_, and $i : E -> CC$, the _current_, such that
  $ phi(e^-) - phi(e^+) = r_e i_e quad "for every edge" e, $
  which is _Ohm's law_, and
  $ sum_(e : e^- = v) i_e - sum_(e : e^+ = v) i_e = I (delta_(v s) - delta_(v t)) quad "for every vertex" v, $
  which is _Kirchhoff's law_.
  The _incidence matrix_ $B$ has rows indexed by $V$ and columns indexed by $E$, with $B_(v e) = 1$ if $v = e^-$, $B_(v e) = -1$ if $v = e^+$, and $B_(v e) = 0$ otherwise.
  With $Y$ the diagonal matrix of the conductances, the _Laplacian_ is $L := B Y B^top$.
  We write $L_t$ for $L$ with the row and the column of $t$ removed, and $L_(s t)$ for $L$ with the rows and the columns of $s$ and $t$ removed; the determinant of an empty matrix is $1$.
] <def:network>

A pair $(phi, i)$ is a flow of value $I$ exactly when $i = Y B^top phi$ and $L phi = I (delta_s - delta_t)$, where $delta_v$ is the vector with entry $1$ at $v$ and $0$ elsewhere.
Reversing the reference direction of an edge changes the sign of a column of $B$, hence leaves $L$ unchanged, and turns flows into flows when the sign of the current in that edge is changed as well; nothing below depends on the reference directions, except where they are fixed explicitly.

The quadratic form of the Laplacian is the power dissipated in the network.
When the real parts of the resistances all have the same sign, its real part is definite on the potentials that are not constant, and this gives the existence and the uniqueness of flows.

#proposition[
  Let $frak(N)$ be a network with resistances such that $re r_e > 0$ for every edge $e$, or such that $re r_e < 0$ for every edge $e$.
  + For every $I$ there is a flow of value $I$, and its potential is unique up to an additive constant.
  + $det L_t != 0$, and for a flow of value $I != 0$ the _impedance_ $Z := (phi(s) - phi(t)) slash I$ equals $det L_(s t) slash det L_t$.
  + The real part of $Z$ has the sign of the numbers $re r_e$.
] <prop:flow>

#proof[
  The numbers $re y_e = re r_e slash abs(r_e)^2$ have the sign of the numbers $re r_e$; suppose that they are positive; the other case is the same.
  For $phi in CC^V$,
  $ overline(phi)^top L phi = sum_e y_e abs(phi(e^-) - phi(e^+))^2. $
  If $L phi = 0$, the real part of this identity shows that $phi$ takes equal values at the two ends of every edge, hence is constant, as $G$ is connected.
  So the kernel of $L$ is the line of constant functions, and $L$ has rank $abs(V) - 1$.
  The image of $L$ lies in the hyperplane of vectors with zero sum, because $bold(1)^top L = 0$, where $bold(1)$ is the vector with all entries $1$, and so equals it.
  This gives the first statement.

  If $L_t phi' = 0$, extend $phi'$ to $phi$ by $phi(t) := 0$; then $(L phi)_v = 0$ for $v != t$, so that $overline(phi)^top L phi = overline(phi(t)) (L phi)_t = 0$, whence $phi$ is constant and $phi' = 0$.
  So $L_t$ is invertible.
  The flow of value $1$ with $phi(t) = 0$ has $phi(s) = (L_t^(-1))_(s s) = det L_(s t) slash det L_t$ by Cramer's rule, and the potential of a flow of value $I$ is $I$ times this one, up to an additive constant; this is the second statement.

  For the flow of value $1$, $overline(phi)^top L phi = overline(phi)^top (delta_s - delta_t) = overline(Z)$, so that
  $ re Z = sum_e re(y_e) abs(phi(e^-) - phi(e^+))^2. $
  This is positive, since $phi$ is not constant.
]

For positive real resistances the potential is largest at one pole and smallest at the other, and the impedance cannot be much smaller than the resistances of the edges at a pole.
In such a network the matrix $L_t$ is real and invertible, so that a flow of real value has a real potential, up to an additive constant.

#proposition[
  Let the resistances of a network be real and positive, and let $(phi, i)$ be a flow of value $I > 0$ with real potential.
  Then $phi(t) <= phi(v) <= phi(s)$ for every vertex $v$, and
  $ 1 / Z <= sum_(e in.rev s) y_e, $
  the sum being over the edges with an end at $s$.
] <prop:maximum>

#proof[
  For an edge $e$ with an end at a vertex $v$, write $v_e$ for its other end.
  Let $A$ be the set of vertices at which $phi$ is largest, and suppose that $s in.not A$.
  At a vertex $v in A$ Kirchhoff's law reads
  $ sum_(e in.rev v) y_e (phi(v) - phi(v_e)) = -I delta_(v t) <= 0, $
  and every term is non-negative, so that every neighbour of $v$ lies in $A$.
  By connectedness $A = V$, which contradicts the fact that $phi$ is not constant, as $I > 0$.
  So $s in A$, and similarly $phi$ is smallest at $t$.
  Kirchhoff's law at $s$ then gives
  $ I = sum_(e in.rev s) y_e (phi(s) - phi(v_e)) <= (phi(s) - phi(t)) sum_(e in.rev s) y_e. $
]

The two determinants are polynomials of low degree in the conductances.

#proposition[
  The determinants $det L_t$ and $det L_(s t)$ are polynomials in the conductances $y_e$ with integer coefficients, homogeneous of degrees $abs(V) - 1$ and $abs(V) - 2$, and of degree at most one in each variable.
] <prop:multilinear>

#proof[
  We have $L = sum_e y_e b_e b_e^top$, where $b_e$ is the column of $B$ of index $e$, and the same holds for the two submatrices, with the vectors $b_e$ truncated.
  Homogeneity is clear, and for a square matrix $A$, a vector $u$ and a variable $y$,
  $ det(A + y u u^top) = det A + y u^top adj(A) u, $
  which has degree at most one in $y$.
]

== The network of a tiling <sec:tiling-network>

The vertices of the network of a tiling are the horizontal lines of the tiling, and its edges are the tiles; the current in a tile is its width, and the potential of a line is its height.
The lines are taken to be the connected components of the union of the horizontal sides, so that the network is also defined when four tiles meet at a point.
@fig:network shows an example.

#definition(name: [network of a tiling])[
  Let $R_1, dots, R_n$ be a tiling $tau$ of the rectangle $[0, W] times [0, H]$, and let $U$ be the union of the top sides and of the bottom sides of its tiles.
  The _network_ $frak(N)(tau)$ of the tiling has as its vertices the connected components of $U$, as its poles the top side $s$ and the bottom side $t$ of the main rectangle, and one edge for each tile, whose tail is the component that contains the top side of the tile and whose head is the component that contains its bottom side.
  The _height_ of a component is the common ordinate of its points, and the _resistance_ of a tile $T$ of width $w_T$ and height $h_T$ is $r_T := h_T slash w_T$.
] <def:tiling-network>

#figure(
  image("figures/network.svg", width: 62%),
  caption: [The tiling of the square by six tiles of proportion $5 slash 3$ of @ex:sporadic, with the components of the union of the horizontal sides of its tiles in bold and each tile represented by the vertical segment through its centre; and its network, in which each tile is an edge of its own colour, with the additional edge $e_0$ of @def:plane-network.],
) <fig:network>

Each component is a horizontal segment of positive length.
A point of the top side of the main rectangle whose abscissa is not that of a corner of a tile lies on the top side of the tile that contains the points just below it; the top side of the main rectangle is the closure of the set of these points, so it is contained in $U$, and it is a component of $U$ because no other point of $U$ has ordinate $H$.
The same holds for the bottom side.
The tiles of the tiling may have any shape.

#proposition[
  Let $tau$ be a tiling of $[0, W] times [0, H]$.
  Then $frak(N)(tau)$ is a network.
  With $phi(C)$ the height of the component $C$ and $i_T := w_T$ for every tile $T$, the pair $(phi, i)$ is a flow of value $W$ for the resistances $r_T$, with $phi(s) - phi(t) = H$.
  Hence $H slash W$ is the impedance of $frak(N)(tau)$ for the resistances $r_T$.
  Moreover $frak(N)(tau)$ has an embedding in the plane in which both poles lie on the outer face.
] <prop:tiling-network>

#proof[
  Ohm's law holds by the choice of the resistances.
  Let $C = [p, q] times {c}$ be a component with $c < H$, and let $(u, c)$ be a point of $C$ whose abscissa is not that of a corner of a tile.
  For small $eta > 0$ the point $(u, c + eta)$ is interior to a tile $T$, the same for all small $eta$.
  If $c$ were interior to the vertical extent of $T$, the point $(u, c)$ would be interior to $T$; but it lies on a side of some tile $T'$, so the interiors of $T$ and $T'$ would meet, and $T' = T$ is impossible.
  So the bottom side of $T$ is at height $c$; it meets $C$ and is connected, so it lies in $C$.
  The tiles whose bottom side lies in $C$ thus cover $C$ up to finitely many points, and their bottom sides do not overlap, so their widths add up to $q - p$.
  In the same way, if $c > 0$, the widths of the tiles whose top side lies in $C$ add up to $q - p$.
  This is Kirchhoff's law at a component other than the poles, and for $s$ and $t$ it gives the value $W$.

  Every component at positive height contains the top side of some tile, whose bottom side lies on a lower component; descending, one reaches $t$, so the graph is connected.
  A tile joins components at different heights, so there are no loops, and $s != t$ because $H > 0$.
  For the embedding, represent each tile by the vertical segment through its centre, between its top and bottom sides, and contract each component to a point.
  The poles are joined by a curve outside the main rectangle, so they lie on a common face, which may be taken as the outer one.
]

== The aspect-ratio function <sec:function>

For a similar tiling of proportion $x$, a tall tile has resistance $x$ and a wide one resistance $1 slash x$.
Keeping the network and the orientations and letting $x$ vary gives a rational function of $x$.

#definition(name: [impedance function])[
  Let $frak(N)$ be a network with $n$ edges and $epsilon$ an orientation vector for its edges.
  The _impedance function_ $Z_(frak(N), epsilon) in QQ(x)$ is the rational function $det L_(s t) slash det L_t$ evaluated at the conductances $y_e = x^(-epsilon_e)$, that is, for the resistances $x^(epsilon_e)$.
  A rational function $F in QQ(x)$ is written _in lowest terms_ as $F = N slash D$ with $N, D in ZZ[x]$ coprime in $QQ[x]$, with no common integer factor other than $plus.minus 1$, and with the leading coefficient of $D$ positive; this determines $N$ and $D$.
] <def:impedance>

By @prop:multilinear the two determinants are then Laurent polynomials in $x$, and the denominator does not vanish at $x = 1$, by @prop:flow; so the definition makes sense, and by @prop:flow the value of $Z_(frak(N), epsilon)$ at any $x > 0$ is the impedance of the network for the resistances $x^(epsilon_e)$.
By @prop:tiling-network, a similar tiling $tau$ of $[0, W] times [0, H]$ of proportion $x$, with an orientation vector $epsilon$, satisfies
$ H / W = Z_(frak(N)(tau), epsilon) (x), $
since the resistance $h_T slash w_T$ of a tile is $x$ if the tile is tall and $1 slash x$ if it is wide.
The impedance function thus gives the height of the main rectangle over its width.
The aspect ratio $W slash H$ of @def:counts is the value at $x$ of the inverse $1 slash Z_(frak(N)(tau), epsilon)$, which is again an impedance function: by @prop:dual, which applies to the network of a tiling by @prop:nonseparable, it is that of the dual network with the orientations reversed.
The statements below are therefore made for impedance functions only.

The next statement collects the properties of these functions.
The first, third and sixth are the classical properties of the impedance of a network of inductors and capacitors, a tall tile corresponding to an inductor and a wide one to a capacitor, and constitute Foster's reactance theorem @foster1924; the second is the corresponding property of positive real functions @brune1931.
For tilings, that the aspect ratio of the main rectangle is a rational function of those of the tiles, with rational coefficients, is a theorem of Dehn @dehn1903; Freiling, Laczkovich and Rinne show that a rectangle of proportion $v$ can be tiled by rectangles of proportion $u$ exactly if $v = Q(u)$ for an odd rational function $Q$ with rational coefficients that maps the right half-plane into itself @flr1997, and Prasolov and Skopenkov state these properties in electrical terms @prasolov2011.
They are proved here from @prop:flow, since the proof is short.

#proposition[
  Let $F = Z_(frak(N), epsilon)$ for a network with $n$ edges, and let $F = N slash D$ in lowest terms.
  + $F(-x) = -F(x)$.
  + For every complex number $x$ with $re x > 0$, $D(x) != 0$ and $re F(x) > 0$. In particular $F$ is finite and positive on $(0, infinity)$.
  + All complex roots of $N$ and of $D$ are simple and lie on the imaginary axis.
  + The coefficients of $N$ and $D$ are non-negative integers. One of $N$ and $D$ is an even polynomial with non-zero constant term, and the other is an odd polynomial in which $x$ has multiplicity one.
  + $deg N - deg D = plus.minus 1$, and $deg N <= n$ and $deg D <= n$. If at most $k$ edges have orientation $+1$, or at most $k$ edges have orientation $-1$, then $deg N <= 2 k + 1$ and $deg D <= 2 k + 1$.
  + There are real numbers $c_infinity >= 0$ and $c_0 >= 0$, and finitely many real numbers $kappa_j > 0$ and $omega_j > 0$, the $omega_j$ being distinct, such that
    $ F(x) = c_infinity x + c_0 / x + sum_j (2 kappa_j x) / (x^2 + omega_j^2). $
    Consequently $F(x) slash x$ is non-increasing and $x F(x)$ is non-decreasing on $(0, infinity)$.
] <prop:reactance>

#proof[
  _First statement._
  Replacing $x$ by $-x$ replaces every conductance $y_e = x^(minus.plus 1)$ by $-y_e$.
  By @prop:multilinear this multiplies $det L_(s t)$ by $(-1)^(abs(V) - 2)$ and $det L_t$ by $(-1)^(abs(V) - 1)$.

  _Second statement._
  If $re x > 0$ then $re x^(plus.minus 1) > 0$.
  By @prop:flow the Laurent polynomial $q := det L_t$ does not vanish at $x$, and $p(x) slash q(x)$, with $p := det L_(s t)$, has positive real part there.
  As rational functions $N q = D p$.
  If $D(x) = 0$ then $N(x) q(x) = 0$, so that $N(x) = 0$, which contradicts coprimality.
  So $D(x) != 0$ and $F(x) = p(x) slash q(x)$.

  _Third statement._
  By the first statement, $N(-x) D(x) = -N(x) D(-x)$.
  As $N$ and $D$ are coprime, $N(x)$ divides $N(-x)$, which has the same degree, so that $N(-x) = plus.minus N(x)$, and then $D(-x) = minus.plus D(x)$.
  So each of $N$ and $D$ is an even or an odd polynomial, and its roots are symmetric about the origin.
  By the second statement neither has a root with positive real part: for $D$ this was shown, and $N(x) = 0$ would give $F(x) = 0$.
  By symmetry neither has a root with negative real part.
  Let $upright(i) omega$, with $omega$ real, be a root of $N$ of multiplicity $m$.
  Then
  $ F(upright(i) omega + rho e^(upright(i) theta)) = A rho^m e^(upright(i) m theta) (1 + O(rho)) $
  with $A != 0$, and by the second statement the real part is positive for $abs(theta) < pi slash 2$.
  Letting $rho$ tend to $0$ gives $re (A e^(upright(i) m theta)) >= 0$ for all $abs(theta) < pi slash 2$.
  For $m >= 2$ the argument $m theta$ covers an interval of length at least $2 pi$, on which this fails.
  So $m = 1$; the same argument applied to $1 slash F$, which also has positive real part on the right half-plane, treats the roots of $D$.

  _Fourth statement._
  A real polynomial with positive leading coefficient whose roots are simple and purely imaginary is a positive multiple of $x^a product_j (x^2 + omega_j^2)$ with $a in {0, 1}$, and has non-negative coefficients.
  The leading coefficient of $N$ is positive because $F > 0$ on $(0, infinity)$.
  By the first statement $N$ and $D$ have opposite parities, so exactly one of them is odd; it is divisible by $x$, exactly once by the third statement, and the other is not divisible by $x$, by coprimality.

  _Fifth statement._
  Let $delta := deg N - deg D$, an odd number by the fourth statement.
  For large $abs(x)$,
  $ F(rho e^(upright(i) theta)) = A rho^delta e^(upright(i) delta theta) (1 + O(1 slash rho)) $
  with $A != 0$, and the argument of the third statement gives $abs(delta) <= 1$.
  Let
  $ P(r) := product_e r_e dot.op det L_(s t) (1 slash r), quad Q(r) := product_e r_e dot.op det L_t (1 slash r), $
  the determinants being evaluated at the conductances $1 slash r_e$.
  By @prop:multilinear these are polynomials in the resistances, of degree at most one in each, and homogeneous of degrees $c + 1$ and $c$, where $c := n - abs(V) + 1$.
  A monomial of $Q$ is a product of $c$ distinct resistances, $j$ of them equal to $x$ and $c - j$ equal to $1 slash x$, so it is $x^(2 j - c)$; if $m$ edges have orientation $-1$ then $c - j <= m$ and $j <= n - m$, so that $x^m$ times the monomial is a power of $x$ with exponent between $0$ and $n$.
  The same holds for $P$.
  So $F = x^m P slash x^m Q$ is a quotient of two polynomials of degree at most $n$, and $N$ and $D$ divide them.
  If at most $k$ edges have orientation $+1$, then $j <= k$ in every monomial, so that the exponents of $Q$ lie between $-c$ and $2 k - c$, and those of $P$ between $-c - 1$ and $2 k - c - 1$; after multiplication by $x^(c + 1)$ both are polynomials of degree at most $2 k + 1$.
  If at most $k$ edges have orientation $-1$, apply this to the function $F(1 slash x)$, which is the impedance function for the reversed orientations.

  _Sixth statement._
  By the third and fifth statements, $F$ has simple poles at some points $plus.minus upright(i) omega_j$ with $omega_j > 0$, possibly a simple pole at $0$, and at infinity $F(x) - c_infinity x$ is bounded, where $c_infinity >= 0$ is the quotient of the leading coefficients of $N$ and $D$ if $deg N > deg D$, and zero otherwise.
  Near a pole $upright(i) omega$, with $omega >= 0$,
  $ F(upright(i) omega + rho e^(upright(i) theta)) = kappa rho^(-1) e^(-upright(i) theta) (1 + O(rho)), $
  and the positivity of the real part for $abs(theta) < pi slash 2$ forces $kappa > 0$.
  For $omega = 0$ this residue is $c_0$, which is taken to be zero if $0$ is not a pole.
  By the first statement the residue at $-upright(i) omega$ is the same as that at $upright(i) omega$, and
  $ kappa / (x - upright(i) omega) + kappa / (x + upright(i) omega) = (2 kappa x) / (x^2 + omega^2). $
  The difference between $F$ and the right-hand side of the formula in the statement is a rational function without poles that is bounded at infinity, hence a constant, and it is odd, hence zero.
  Finally
  $
    F(x) / x = c_infinity + c_0 / x^2 + sum_j (2 kappa_j) / (x^2 + omega_j^2), quad x F(x) = c_infinity x^2 + c_0 + sum_j (2 kappa_j x^2) / (x^2 + omega_j^2).
  $
]

By the fifth statement $F(x)$ tends to $0$ or to $infinity$ as $x$ tends to infinity, and by the fourth it does likewise as $x$ tends to $0$ from the right.
Reversing all orientations replaces $F(x)$ by $F(1 slash x)$, since it inverts every resistance as a function of $x$.

For the square, the proportions are among the roots in $[1, infinity)$ of the polynomials $N - D$.
Since $N$ and $D$ have opposite parities, such a polynomial retains all the information of the function.

#proposition[
  For $F = N slash D$ as in @prop:reactance, the polynomial $N - D$ is primitive, and it determines the unordered pair ${F, 1 slash F}$; so does $D - N$, and so does the pair ${N - D, D - N}$.
] <prop:difference>

#proof[
  By the fourth statement of @prop:reactance, $N$ and $D$ have no monomial in common, so the coefficients of $N - D$ are those of $N$ and of $-D$, whose greatest common divisor is $1$.
  Let $P := plus.minus (N - D)$, and let $P_0$ and $P_1$ be its even and odd parts.
  Then ${N, D} = {plus.minus P_0, plus.minus P_1}$, and the signs are those that make the leading coefficients positive.
  So $P$ determines ${N, D}$, and hence ${N slash D, D slash N}$.
]

The behaviour of $F$ at the two ends of $(0, infinity)$ fixes the signs of $N - D$ there, and hence the parity of the number of its positive roots.

#proposition[
  For $F = N slash D$ as in @prop:reactance, let $d := deg(N - D)$, and let $rho.alt$ be the number of roots of $N - D$ in $(0, infinity)$, counted with multiplicity; these roots are the solutions of $F(x) = 1$.
  If $F$ tends to $0$ at one end of $(0, infinity)$ and to $infinity$ at the other, then $d$ and $rho.alt$ are odd; otherwise both are even.
] <prop:parity-full>

#proof[
  We have $d = max(deg N, deg D)$, and the leading coefficient of $N - D$ is positive if $deg N > deg D$, that is, if $F$ tends to $infinity$ at infinity, and negative otherwise.
  Exactly one of $N(0)$ and $D(0)$ is zero, so $N(0) - D(0)$ is negative if $N$ is the odd polynomial, that is, if $F$ tends to $0$ at $0$, and positive otherwise.
  The number $rho.alt$ is odd exactly when the value at $0$ and the leading coefficient have opposite signs.
  The four cases are as follows.
  - If $F$ tends to $0$ at $0$ and to $infinity$ at infinity, the signs are opposite, and $d = deg N$ is odd, as $N$ is odd.
  - If $F$ tends to $infinity$ at $0$ and to $0$ at infinity, the signs are opposite, and $d = deg D$ is odd, as $D$ is odd.
  - If $F$ tends to $0$ at both ends, the signs agree, and $d = deg D = deg N + 1$ is even, as $N$ is odd.
  - If $F$ tends to $infinity$ at both ends, the signs agree, and $d = deg N = deg D + 1$ is even, as $D$ is odd.
]

In the first case of the statement $F(x) = 1$ has a positive solution $x$, and either $x >= 1$, or $1 slash x >= 1$ is a solution for the reversed orientations.
The number $d$ is the degree of $N - D$, and not that of the minimal polynomial of a proportion, which divides $N - D$; the relation between this law and the distribution of the degrees in @tab:degrees and @tab:degrees-high therefore remains heuristic.
A function of the first kind always yields a positive solution, and one of the second kind usually yields none, which would explain why the proportions of odd degree make up between $82$ and $90$ per cent of all proportions for $7 <= n <= 13$.

The derivative of an impedance function has a geometric meaning.

#proposition[
  Let $F = Z_(frak(N), epsilon)$, let $x > 0$, and let $i$ be the current of the flow of value $1$ for the resistances $r_e = x^(epsilon_e)$.
  Then
  $ F(x) = sum_e r_e i_e^2, quad x F'(x) = sum_e epsilon_e r_e i_e^2. $
  In particular, for a similar tiling of proportion $x > 1$ with network $frak(N)$ and orientation vector $epsilon$, the number $x F'(x) slash F(x)$ is the area of the tall tiles minus the area of the wide tiles, divided by the area of the main rectangle.
] <prop:slope>

#proof[
  Let $(phi, i)$ be the flow of value $1$ for positive real resistances $r$, and let $j$ be a real function on the edges that satisfies Kirchhoff's law with value $c$.
  Multiplying Kirchhoff's law for $j$ at each vertex $v$ by $phi(v)$ and summing gives $sum_e (phi(e^-) - phi(e^+)) j_e = c (phi(s) - phi(t))$, that is, $sum_e r_e i_e j_e = c Z$, where $Z$ is the impedance.
  With $j = i$ this is $Z = sum_e r_e i_e^2$.
  The currents are rational functions of the resistances, by Cramer's rule and @prop:flow; let a dot denote the derivative along a differentiable family of resistances.
  Then $dot(i)$ satisfies Kirchhoff's law with value $0$, so that $sum_e r_e i_e dot(i)_e = 0$, and $dot(Z) = sum_e dot(r)_e i_e^2 + 2 sum_e r_e i_e dot(i)_e = sum_e dot(r)_e i_e^2$.
  For $r_e = x^(epsilon_e)$ the derivative with respect to $x$ is $dot(r)_e = epsilon_e r_e slash x$.
  In the tiling the tile of $e$ has width $i_e W$ and height $r_e i_e W$, where $W$ is the width of the main rectangle, by @prop:tiling-network, so that its area is $r_e i_e^2 W^2$ and the area of the main rectangle is $F(x) W^2$.
]

Since $abs(x F'(x)) <= F(x)$, this again proves that $F(x) slash x$ is non-increasing and $x F(x)$ non-decreasing.
At a solution $x > 1$ of $F(x) = 1$ at which no current vanishes and $F'(x) > 0$, the tall tiles of the corresponding tiling of the square cover more than half of it, and at one with $F'(x) < 0$, less than half.

== From a network to a tiling <sec:converse>

The correspondence of Brooks, Smith, Stone and Tutte has a converse @bsst1940: a planar network with positive resistances in which every current is non-zero gives a tiling with one tile for each edge, whose own network is obtained from the given one by identifying vertices of equal potential that lie on a common face.
The abscissas of the tiling are given by a potential on the faces of the network, which exists by planarity.

#definition(name: [plane network])[
  A _plane network_ is a network together with an embedding of its graph $G$ in the plane in which both poles lie on the outer face.
  For a plane network, $G^+$ is the plane graph obtained from $G$ by adding an edge $e_0$ from $t$ to $s$ inside the outer face.
  For an edge $e$ of $G^+$ with a direction, $lft(e)$ and $rgt(e)$ are the faces of $G^+$ on the left and on the right of $e$, and we put $f_R := lft(e_0)$ and $f_L := rgt(e_0)$.
] <def:plane-network>

Embeddings are taken to be piecewise linear, so that the two sides of a closed curve are well defined, and the dual of a plane graph is a multigraph, in which a minimal cut of two edges gives a cycle of length two.
By @prop:tiling-network the network of a tiling is a plane network, for the embedding constructed there, and it is always considered with that embedding.

The graph $G^+$ of the network of a tiling is a non-separable planar map, in the sense of @sec:growth; this is used there for the upper bound on $a(n)$.

#proposition[
  Let $tau$ be a tiling of a rectangle with $n >= 1$ tiles.
  Then the plane graph $G^+$ of the plane network $frak(N)(tau)$ is a non-separable planar map with $n + 1$ edges.
] <prop:nonseparable>

#proof[
  Direct each edge from the top of its tile to the bottom.
  The height decreases along the edges, every component other than $s$ contains the bottom side of a tile, and every component other than $t$ the top side of one, by the proof of @prop:tiling-network.
  So from every vertex $v$ a directed path leads down to $t$, and one leads up from $v$ to $s$ following the edges backwards; the first passes only through vertices lower than $v$ and the second only through higher ones.
  Remove a vertex $u$.
  If $u = s$, every other vertex still reaches $t$; similarly if $u = t$.
  Otherwise each remaining vertex $v$ still has its path to $t$ or its path to $s$, since $u$ is not both lower and higher than $v$, and $s$ and $t$ are joined by $e_0$.
  So $G^+$ has no vertex whose removal disconnects it; it has no loop, and it has $n + 1$ edges.
]

In particular $G^+$ has no bridge, for a bridge of a connected graph without loops that has at least two edges has an end whose removal disconnects the graph; this is what the application of @prop:dual to the network of a tiling requires.

The first step is the potential on the faces, whose differences across the edges are the currents.
It uses Euler's formula, by which a connected plane graph with $v$ vertices and $m$ edges has $m - v + 2$ faces.

#proposition[
  Let $(phi, i)$ be a flow of value $I$ on a plane network.
  Then there is a function $psi$ on the faces of $G^+$, unique up to an additive constant, such that $psi(lft(e)) - psi(rgt(e)) = i_e$ for every edge $e$ of $G$, taken in its reference direction, and $psi(f_R) - psi(f_L) = I$.
] <prop:face-potential>

#proof[
  Put $j_e := i_e$ for the edges of $G$ and $j_(e_0) := I$; by Kirchhoff's law $j$ is a circulation on $G^+$, that is, at every vertex the values of $j$ on the edges that leave it and on those that enter it have equal sums.
  The map $partial$ that sends a function $psi$ on the faces to the function $e |-> psi(lft(e)) - psi(rgt(e))$ on the edges takes its values in the circulations, because around a vertex the contributions telescope.
  Its kernel consists of the constants, because the dual graph is connected.
  The space of circulations of the connected plane graph $G^+$, which has $n + 1$ edges if $G$ has $n$, has dimension $(n + 1) - abs(V) + 1$, which by Euler's formula is one less than the number of faces; so $partial$ maps onto it.
]

The second step is the construction of the tiling.
Its proof is complete given three standard facts: Euler's formula, used in @prop:face-potential; the Jordan curve theorem; and the duality between the bonds and the cycles of a connected plane graph, by which a set of edges is a minimal cut exactly when the dual edges form a cycle of the dual graph @diestel2017[Section 4.6].
The duality is used in its oriented form: if the edges of a minimal cut are all directed from one side of the cut to the other, they all cross the dual cycle in the same sense.
This follows from the unoriented statement, since the dual cycle separates the two sides of the cut, by the Jordan curve theorem.

#proposition[
  Let $frak(N)$ be a plane network with positive real resistances, and let $(phi, i)$ be a flow of value $I > 0$, with real potential, in which no current $i_e$ is zero.
  Direct every edge so that $i_e > 0$, and let $psi$ be as in @prop:face-potential.
  Then the rectangles
  $ rct(e) := [psi(rgt(e)), psi(lft(e))] times [phi(e^+), phi(e^-)], quad e in E, $
  form a tiling of the rectangle $[psi(f_L), psi(f_R)] times [phi(t), phi(s)]$ with $abs(E)$ tiles, and $rct(e)$ has width $i_e$ and height $r_e i_e$.
] <prop:bsst>

#proof[
  By Ohm's law, $phi$ decreases strictly along every directed edge, so the directions are acyclic.
  By @prop:maximum, $phi$ is largest at $s$ and smallest at $t$, so no edge enters $s$ or leaves $t$.
  A vertex $v$ other than the poles has an edge, and by Kirchhoff's law the currents entering it and those leaving it have equal sums, so it has both an entering and a leaving edge.
  Following entering edges backwards from any vertex therefore leads to $s$, and following leaving edges leads to $t$.

  Let $c$ be a real number with $phi(t) < c < phi(s)$, different from every value of $phi$, let $U_c$ be the set of vertices at which $phi > c$, and let $D_c$ be its complement.
  A directed path from $s$ to a vertex of $U_c$ stays in $U_c$, so $U_c$ induces a connected subgraph; so does $D_c$.
  Let $E_c$ be the set of edges of $G$ between the two; every one of them is directed from $U_c$ to $D_c$, and $E_c$ is the set of edges $e$ with $phi(e^+) < c < phi(e^-)$.
  In $G^+$ the set $E_c union {e_0}$ is a cut both of whose sides are connected, hence a minimal cut.
  By duality there is a closed curve $gamma$ that passes through distinct faces $f_0, f_1, dots, f_(m - 1)$ of $G^+$ in cyclic order, meets $G^+$ only in one interior point of each edge of the cut, and crosses these edges one at a time.
  By the Jordan curve theorem $gamma$ separates the plane into two regions; the connected sets $U_c$ and $D_c$ lie in different ones, since an edge of the cut crosses $gamma$ once.
  Traverse $gamma$ with $U_c$ on the left.
  Each edge $e in E_c$ runs from the left of $gamma$ to its right, so $gamma$ crosses it from $rgt(e)$ to $lft(e)$, and $psi$ increases by $i_e$ at the crossing.
  The edge $e_0$ runs from the right of $gamma$ to its left, so $gamma$ crosses it from $lft(e_0) = f_R$ to $rgt(e_0) = f_L$.
  Starting after that crossing, $gamma$ visits $f_L = f_0, f_1, dots, f_(m - 1) = f_R$ and crosses the edges $e_1, dots, e_(m - 1)$ of $E_c$, and the interval $[psi(f_(j - 1)), psi(f_j)]$ is the horizontal extent of $rct(e_j)$.
  So the rectangles that meet the horizontal line at height $c$ are those of the edges of $E_c$, and their sections subdivide the segment $[psi(f_L), psi(f_R)] times {c}$.

  This holds for all but finitely many $c$.
  Every rectangle meets such a line, so it lies in the main rectangle.
  Two rectangles whose interiors intersected would have overlapping sections on such a line.
  The union of the rectangles is closed and contains every point of the main rectangle at such a height, hence all of it.
  The width of $rct(e)$ is $i_e$ by the choice of $psi$, and its height is $r_e i_e$ by Ohm's law.
]

The additive constants of $phi$ and $psi$ may be chosen so that the main rectangle is $[0, I] times [0, Z I]$, where $Z$ is the impedance.

The third step is that the inverse of an impedance function of a plane network is the impedance function of the dual network, in which currents and potential differences are exchanged.
For a tiling this is transposition.

#proposition[
  Let $frak(N)$ be a plane network such that $G^+$ has no bridge.
  Let $frak(N)^*$ consist of the graph whose vertices are the faces of $G^+$, with an edge $e^*$ joining $lft(e)$ and $rgt(e)$ for every edge $e$ of $G$, and of the poles $f_R$ and $f_L$.
  + $frak(N)^*$ is a plane network, and $Z_(frak(N)^*, -epsilon) = 1 slash Z_(frak(N), epsilon)$ for every orientation vector $epsilon$.
  + For positive real resistances $r_e$ on $frak(N)$ and $1 slash r_e$ on $frak(N)^*$, the current in $e^*$ for a flow of non-zero value on $frak(N)^*$ vanishes exactly when the current in $e$ for a flow of non-zero value on $frak(N)$ does.
] <prop:dual>

#proof[
  The graph of $frak(N)^*$ is the dual of $G^+$ with the edge dual to $e_0$ removed, that is, the dual of the plane graph $G^+ slash e_0$ obtained by contracting $e_0$.
  It is connected, it has no loop because $G^+$ has no bridge, its poles are distinct because $e_0$ is not a bridge, and they lie on the face that corresponds to the vertex of $G^+ slash e_0$ formed by $s$ and $t$.
  Let $(phi, i)$ be a flow of value $I != 0$ on $frak(N)$ for positive real resistances $r$, and let $psi$ be as in @prop:face-potential.
  On $frak(N)^*$ take the potential $psi$ and, in the edge $e^*$ directed from $lft(e)$ to $rgt(e)$, the current $r_e i_e = phi(e^-) - phi(e^+)$.
  Ohm's law holds with the resistance $1 slash r_e$.
  Kirchhoff's law at a face says that the differences of $phi$ along the edges of its boundary, other than $e_0$, add up to zero, or to $plus.minus (phi(s) - phi(t))$ for the two faces at $e_0$; this holds because the boundary is a closed walk.
  So this is a flow of value $phi(s) - phi(t)$ on $frak(N)^*$ with potential difference $I$ between the poles, and the impedance of $frak(N)^*$ is the inverse of that of $frak(N)$.
  For the resistances $x^(epsilon_e)$ this holds for all $x > 0$, hence as an identity of rational functions.
  In the flow constructed, the current in $e^*$ is $r_e$ times the current in $e$; every flow of non-zero value on either network is a non-zero multiple of the one considered, up to an additive constant of the potential, by @prop:flow, which gives the second statement.
]

== Wide rectangles <sec:wide>

For a network with an orientation vector, the current $i_e$ of the flow of value $1$ is a rational function of $x$, by Cramer's rule.
It may vanish identically, and the pair then has no tile for that edge at any proportion; such pairs must be left out of the count of the functions.

#definition(name: [proper pair])[
  A pair $(frak(N), epsilon)$ of a plane network with $n$ edges and an orientation vector for its edges is _proper_ if no current $i_e$ of the flow of value $1$ for the resistances $x^(epsilon_e)$ vanishes identically as a function of $x$.
  We write $cal(F)_n$ for the set of impedance functions $Z_(frak(N), epsilon)$ of the proper pairs with $n$ edges, and $cal(F)_n^infinity$ for the set of those $F in cal(F)_n$ that tend to $infinity$ at infinity.
] <def:proper>

The set $cal(F)_n$ consists of the impedance functions that tilings with $n$ tiles realise, in the following sense.

#proposition[
  Let $n >= 1$.
  + The set $cal(F)_n$ is finite and closed under $F |-> 1 slash F$, and $F != 1 slash F$ for every $F in cal(F)_n$. So $abs(cal(F)_n)$ is even, and we put $E(n) := abs(cal(F)_n) slash 2$.
  + If $tau$ is a similar tiling of $[0, W] times [0, H]$ of proportion $x$ with $n$ tiles, and $epsilon$ is an orientation vector of $tau$, then $(frak(N)(tau), epsilon)$ is proper and $Z_(frak(N)(tau), epsilon) (x) = H slash W$.
  + If $(frak(N), epsilon)$ is proper, then for every $x > 0$ at which no current vanishes, in particular for all but finitely many $x > 0$, there is a tiling of the rectangle $[0, 1] times [0, Z_(frak(N), epsilon) (x)]$ with $n$ tiles in which the tile of the edge $e$ has height $x^(epsilon_e)$ times its width.
] <prop:functions>

#proof[
  For the first statement, there are finitely many networks with $n$ edges up to isomorphism, and the function depends only on the isomorphism class of the network with its orientation vector.
  A bridge of $G^+$ carries no current: its removal leaves both poles in one component, as they are joined by $e_0$, and the sum of Kirchhoff's law over the vertices of the other component is, up to sign, the current in the bridge.
  The edge $e_0$ is not a bridge, since $G$ is connected.
  So $G^+$ has no bridge when the pair is proper, and @prop:dual applies; its second statement, applied at every $x > 0$, shows that the dual pair $(frak(N)^*, -epsilon)$ is proper, and its first statement that the impedance function of the dual pair is $1 slash F$.
  Finally $F = 1 slash F$ would give $F^2 = 1$, which is impossible for an odd function.

  The second statement is @prop:tiling-network, noting that the currents of the flow of the tiling are the widths of the tiles, which are not zero, and that the flow of value $1$ at the proportion $x$ is that flow divided by $W$, by @prop:flow.

  The third statement is @prop:bsst with $I = 1$, with the edges directed so that the currents are positive and the additive constants chosen as in the remark that follows that proposition.
]

In the third statement, the tiling is similar of proportion $x$ if $x >= 1$.
By the second and third statements, $cal(F)_n$ is also the set of functions $Z_(frak(N)(tau), epsilon)$ over all similar tilings $tau$ with $n$ tiles, of any proportion and of any main rectangle, and their orientation vectors $epsilon$.
Indeed, for a proper pair $(frak(N), epsilon)$, the third statement gives a tiling $tau_x$ for all but finitely many $x >= 1$; the networks $frak(N)(tau_x)$, with their edges labelled by those of $frak(N)$, take finitely many values up to isomorphism, so one of them occurs for infinitely many $x$, and by the second statement its function agrees with $Z_(frak(N), epsilon)$ at these $x$, hence everywhere.

#example[
  The pairs with an identically vanishing current have to be left out.
  Consider the network of a pinwheel of five tiles, four around a central one as in @fig:pinwheel, with all orientations equal.
  The current in the central edge vanishes identically, and the impedance function is $x$ or $1 slash x$.
  This function does not belong to $cal(F)_5$.
  Since $cal(F)_5$ is closed under inversion, it suffices to consider $1 slash x$.
  The non-zero currents of a proper pair with five edges have no zero at $x >= 17$, by the fourth step of the proof of @prop:threshold below; if $1 slash x$ were the impedance function of a proper pair with five edges, the third statement of @prop:functions would therefore give a similar tiling of proportion $1009$ of the rectangle $[0, 1] times [0, 1 slash 1009]$ with five tiles, so that $1009 in P_5 (1009)$ by @prop:scaling, and the search finds that this is not so.
  The exclusion therefore rests on a computation, and on Kirchhoff's formulas, which @prop:threshold assumes.
] <ex:improper>

By the fifth statement of @prop:reactance, each $F in cal(F)_n$ tends to $infinity$ or to $0$ at infinity.
Inversion exchanges the two kinds, so that $abs(cal(F)_n^infinity) = E(n)$.
A function of the first kind takes each large value exactly once on $[1, infinity)$, and for a wide main rectangle this identifies the proportions with these functions.

#proposition[
  For every $n >= 1$ there is a real number $W(n)$ such that, for every real number $w > W(n)$:
  + every $F in cal(F)_n^infinity$ has exactly one solution $x_F (w)$ of $F(x) = w$ in $[1, infinity)$;
  + the map $F |-> x_F (w)$ is a bijection from $cal(F)_n^infinity$ onto $P_n (w)$.
  In particular $a_w (n) = E(n)$ for every real number $w > W(n)$.
] <prop:wide-full>

#proof[
  Each $F in cal(F)_n$ is continuous on $[1, infinity)$, by the second statement of @prop:reactance.
  The proof consists of five steps, each of which gives finitely many lower bounds on $w$.

  _First step._
  If $F in cal(F)_n without cal(F)_n^infinity$ then $F$ is bounded on $[1, infinity)$, by $beta_F$ say.

  _Second step._
  If $F in cal(F)_n^infinity$ then $F(x) slash x$ tends to $c_infinity > 0$ and $F'(x)$ tends to $c_infinity$ at infinity, as for any rational function.
  So there is $X_F >= 1$ such that $F$ is strictly increasing on $[X_F, infinity)$.
  For $X >= X_F$ put $mu_F (X) := max_([1, X]) F$.
  If $w > mu_F (X)$ then $F(x) = w$ has exactly one solution in $[1, infinity)$, and it is larger than $X$.

  _Third step._
  If $F != G$ in $cal(F)_n^infinity$, the two functions agree at finitely many points; let $X_(F G) >= X_F$ exceed all of them.
  If $w > mu_F (X_(F G))$ and $w > mu_G (X_G)$ then $x_F (w) != x_G (w)$.

  _Fourth step._
  For $F in cal(F)_n^infinity$ choose a proper pair $(frak(N), epsilon)$ with $Z_(frak(N), epsilon) = 1 slash F$, which exists by the first statement of @prop:functions, and let $X'_F >= X_F$ exceed every positive zero of its currents.
  If $w > mu_F (X'_F)$ then no current vanishes at $x = x_F (w)$, and the third statement of @prop:functions gives a similar tiling of proportion $x$ of the rectangle $[0, 1] times [0, 1 slash w]$ with $n$ tiles.
  By @prop:scaling, $x_F (w) in P_n (w)$.

  _Fifth step._
  Let $x in P_n (w)$, and let $tau$ be a similar tiling of $[0, w] times [0, 1]$ of proportion $x$ with $n$ tiles, with an orientation vector $epsilon$.
  By the second and first statements of @prop:functions, $F := 1 slash Z_(frak(N)(tau), epsilon)$ belongs to $cal(F)_n$ and $F(x) = w$.
  If $w$ exceeds every bound $beta_F$ of the first step, then $F in cal(F)_n^infinity$, and $x = x_F (w)$ by the second step.

  Let $W(n)$ be the largest of the finitely many bounds of the five steps.
]

The rationality of $w$ is not used.

The threshold can be made explicit by bounding the coefficients of the polynomials involved, which is done by counting spanning trees.
The following formulas of Kirchhoff, for a network with conductances $y$, are assumed @kirchhoff1847; in the generality needed they are instances of the all-minors matrix-tree theorem @chaiken1982.
- $det L_t = sum_T product_(e in T) y_e$, the sum being over the spanning trees $T$ of $G$.
- $det L_(s t) = sum_Phi product_(e in Phi) y_e$, the sum being over the spanning forests $Phi$ of $G$ with two components, one containing each pole.
- For the flow of value $1$, $i_e det L_t = sum_T plus.minus product_(f in T) y_f$, the sum being over the spanning trees $T$ that contain $e$ and whose path between the poles passes through $e$.

#proposition[
  @prop:wide-full holds with $W(n) = n (1 + 4^n slash 2)$.
] <prop:threshold>

#proof[
  Let $(frak(N), epsilon)$ be a pair of a plane network with $n$ edges and an orientation vector, $m$ of the edges having orientation $-1$, and let $F = Z_(frak(N), epsilon) = N slash D$ in lowest terms.
  Multiply the three sums of Kirchhoff's formulas by $x^m product_e r_e$, where $r_e = x^(epsilon_e)$: as in the proof of the fifth statement of @prop:reactance, this gives polynomials $tilde(P)$, $tilde(Q)$ and $nu_e$ in $x$ with integer coefficients such that $F = tilde(P) slash tilde(Q)$ and $i_e = nu_e slash tilde(Q)$, where the coefficients of $tilde(P)$ and $tilde(Q)$ are non-negative.
  The number $tilde(Q)(1)$ is the number of spanning trees, which is at most $binom(n, abs(V) - 1)$; $tilde(P)(1)$ is at most $binom(n, abs(V) - 2)$; and the sum of the absolute values of the coefficients of $nu_e$ is at most $tilde(Q)(1)$.
  Each binomial coefficient is at most $binom(n, floor(n slash 2)) <= 2^(n - 1)$.
  Write $tilde(P) = g N$ and $tilde(Q) = g D$.
  Then $g in ZZ[x]$: write $g = (a slash b) g_0$ with $g_0 in ZZ[x]$ primitive and $a slash b$ a fraction in lowest terms; by Gauss's lemma $b$ divides the content of $N$ and that of $D$, which have no common factor since $N slash D$ is in lowest terms, so that $b = 1$.
  The roots of $g$ are roots of $tilde(Q)$, which lie on the imaginary axis: $tilde(Q)$ has no root with positive real part by @prop:flow, and none with negative real part because $tilde(Q)(-x) = plus.minus tilde(Q)(x)$ by @prop:multilinear.
  So $g$ is a real multiple of a product of factors $x$ and $x^2 + omega^2$, its coefficients all have the same sign, and $abs(g(1)) >= 1$.
  Hence $N(1) <= 2^(n - 1)$ and $D(1) <= 2^(n - 1)$, and these numbers bound every coefficient of $N$ and of $D$.
  We use Cauchy's bound: a root $z$ of a polynomial with integer coefficients $a_0, dots, a_d$, where $a_d != 0$, satisfies $abs(z) < 1 + max_j abs(a_j)$.
  By @prop:maximum, every $F in cal(F)_n$ satisfies $F(x) <= n x$ for $x >= 1$, because $1 slash F in cal(F)_n$ is an impedance function, and the conductances are at most $x$.
  Now let $w > n (1 + 4^n slash 2)$, and follow the five steps of the proof of @prop:wide-full.

  _First step._
  If $F in cal(F)_n without cal(F)_n^infinity$, then $x F(x)$ is non-decreasing, with limit the quotient of the leading coefficients of $N$ and $D$, which is at most $2^(n - 1)$; so $F <= 2^(n - 1) < w$ on $[1, infinity)$.

  _Second step._
  Let $F in cal(F)_n^infinity$, and write $F(x) = c_infinity x + G(x)$ in the notation of the sixth statement of @prop:reactance.
  Then $G'(x) >= -K slash x^2$ with $K := c_0 + sum_j 2 kappa_j = lim_(x -> infinity) x G(x)$, because $abs(omega^2 - x^2) <= omega^2 + x^2$.
  If $N = a_d x^d + a_(d - 2) x^(d - 2) + dots.c$ and $D = b_(d - 1) x^(d - 1) + dots.c$, then $c_infinity = a_d slash b_(d - 1)$ and $K <= a_(d - 2) slash b_(d - 1)$, so that $K slash c_infinity <= a_(d - 2) slash a_d <= 2^(n - 1)$.
  So $F$ is strictly increasing on $[X_0, infinity)$, where $X_0 := 2^((n - 1) slash 2)$.
  A solution $x >= 1$ of $F(x) = w$ satisfies $x >= w slash n > X_0$, and $F(X_0) <= n X_0 < w$; so there is exactly one solution $x_F (w)$, and $x_F (w) >= w slash n > 1 + 4^n slash 2$.

  _Third step._
  If $F != G$ in $cal(F)_n^infinity$, with $F = N_F slash D_F$ and $G = N_G slash D_G$ in lowest terms, a common solution of $F(x) = w$ and $G(x) = w$ is a root of $N_F D_G - N_G D_F$, a non-zero polynomial with integer coefficients of absolute value at most $2 dot.op 4^(n - 1)$; its roots are smaller than $1 + 4^n slash 2$.

  _Fourth step._
  A zero of a current of a proper pair is a root of some $nu_e != 0$, hence smaller than $1 + 2^(n - 1)$.

  _Fifth step._
  This step is covered by the first and the second.
]

The bound is not sharp: for $n <= 9$ the counts are observed to be constant from $w = floor(n^2 slash 4) + 2$ onwards.
The next statement shows that the two statements of @prop:wide-full cannot both hold below that width, by exhibiting two functions with a common solution.

#proposition[
  Let $n >= 2$, and let $a, b >= 1$ be integers with $a + b = n$.
  For $w = a b + 1$, two distinct functions of $cal(F)_n^infinity$ have the common solution $x = b$ of $F(x) = w$, and $b in P_n (w)$.
  Consequently the two statements of @prop:wide-full do not both hold for $w = floor(n^2 slash 4) + 1$, and every $W(n)$ for which that proposition holds is at least $floor(n^2 slash 4) + 1$.
] <prop:coincidence>

#proof[
  Place $a$ wide tiles of height $1$ side by side, of total width $a x$, and beside them a block of $b$ tiles, of total height $1$.
  If the $b$ tiles are tall and side by side, the block has width $b slash x$; if they are wide and stacked, it has width $x slash b$.
  The functions $a x + b slash x$ and $a x + x slash b$ are different; they are the inverses of the impedance functions of these two tilings, so they belong to $cal(F)_n$ by the second and first statements of @prop:functions, and they tend to $infinity$ at infinity; and they take the value $a b + 1$ at $x = b$.
  The largest value of $a b$ is $floor(n^2 slash 4)$.
]

@prop:coincidence does not give $a_w (n) < E(n)$ at the width $w = a b + 1$, because a function may contribute several solutions when $w$ is small.
It exhibits one coincidence for even $n$, where $a = b$, and two for odd $n$, where $(a, b)$ and $(b, a)$ give the same width; in the computations, which cover $2 <= n <= 9$, $a_w (n)$ at $w = floor(n^2 slash 4) + 1$ is accordingly $E(n) - 1$ for even $n$ and $E(n) - 2$ for odd $n$.
#conjecture[
  For every $n$ and every rational $w > 0$, $a_w (n) <= E(n)$; and $a_w (n) = E(n)$ for every integer $w >= floor(n^2 slash 4) + 2$.
] <conj:threshold>

The first part of @conj:threshold holds for $n <= 8$ on the thirty integers and sixteen fractions tried; the second holds for $n <= 8$ and $w <= 30$, and was predicted and then confirmed for $n = 9$.
What is missing for the second part of @conj:threshold is a proof that beyond that width no two functions share a solution, every function of $cal(F)_n^infinity$ has one solution, the functions of the other kind have none, and no tile vanishes.
The gap between the width proved sufficient, which is exponential in $n$, and the conjectured one, which is quadratic, comes from the use of Cauchy's bound on the roots of $N_F D_G - N_G D_F$.
For the first part of @conj:threshold we have no argument: for small $w$ a function can have several solutions and the functions of the other kind contribute as well, and the trivial bound is $a_w (n) <= 2 n E(n)$.

The column of functions in @tab:structure was computed with $w = 1009$, and confirmed with three larger values of $w$ for $n <= 9$ and one for $n = 10$.
The largest of these, $w = 1000003$, exceeds $n (1 + 4^n slash 2)$ for $n <= 8$, so that for these $n$ the column is $E(n)$ by @prop:wide-full and @prop:threshold; for $9 <= n <= 11$ the widths used are below that threshold, and the identification of the column with $E(n)$ depends on the second part of @conj:threshold.
For $n <= 10$ the column agrees with the counts of distinct functions reported by Einstein @einstein2023, obtained by enumerating networks; the value $9865302$ for $n = 11$ is new and was computed once.


The number of functions at least triples with each tile.

#proposition[
  For every $n >= 1$, $E(n + 1) >= 3 E(n)$.
  Consequently $E(n) >= 3^(n - 1)$, and $a_w (n + 1) >= 3 a_w (n)$ for every real number $w > (n + 1) (1 + 4^(n + 1) slash 2)$.
] <prop:functions-growth>

#proof[
  Let $(frak(N), epsilon)$ be a proper pair with $n$ edges and impedance function $F$, and let $delta in {+1, -1}$.
  Let $frak(N)'$ be obtained from $frak(N)$ by adding a vertex $s'$ and an edge $e'$ from $s'$ to $s$, with poles $s'$ and $t$, and let $epsilon'$ extend $epsilon$ by $epsilon'_(e') := delta$.
  Drawing $s'$ and $e'$ in the outer face gives an embedding in which $s'$ and $t$ lie on the outer face, so that $frak(N)'$ is a plane network.
  Let $x > 0$, and let $(phi, i)$ be the flow of value $1$ of $frak(N)$ for the resistances $x^(epsilon_e)$.
  Extending it by $phi(s') := phi(s) + x^delta$ and $i_(e') := 1$ gives a flow of value $1$ of $frak(N)'$: Ohm's law holds on $e'$, and Kirchhoff's law holds at $s$, where the current $1$ that enters by $e'$ replaces the value of the flow.
  By @prop:flow it is the flow of value $1$ of $frak(N)'$, so that the impedance of $frak(N)'$ is $F(x) + x^delta$, and its currents are those of $frak(N)$ and the constant $1$.
  Hence $(frak(N)', epsilon')$ is proper, and its impedance function agrees with $F + x^delta$ at every $x > 0$, hence identically.
  So the sets $S_+ := {F + x : F in cal(F)_n}$ and $S_- := {F + 1 slash x : F in cal(F)_n}$ are contained in $cal(F)_(n + 1)$, and each has $2 E(n)$ elements.

  Let $G in S_+ inter S_-$, say $G = F_1 + x = F_2 + 1 slash x$ with $F_1, F_2 in cal(F)_n$.
  Then $F_1 (x) = F_2 (x) + 1 slash x - x > 1 slash x - x$ on $(0, infinity)$, by the second statement of @prop:reactance, so that $F_1$ tends to $infinity$ at $0$.
  By the fourth statement of @prop:reactance every element of $cal(F)_n$ tends to $0$ or to $infinity$ at $0$, and inversion exchanges the two kinds, so that $E(n)$ elements of $cal(F)_n$ tend to $infinity$ at $0$.
  As $G$ determines $F_1$, the intersection has at most $E(n)$ elements, and $S := S_+ union S_-$ has at least $3 E(n)$.

  The inverses of the elements of $S$ belong to $cal(F)_(n + 1)$, by the first statement of @prop:functions.
  They are not in $S$: an element $F + x^delta$ of $S$ takes the value $F(1) + 1 > 1$ at $1$, and its inverse a value smaller than $1$.
  Hence $2 E(n + 1) >= 2 abs(S) >= 6 E(n)$.
  The second statement follows from $E(1) = 1$, since the functions of the network with one edge are $x$ and $1 slash x$, and the third from @prop:wide-full and @prop:threshold, since the threshold $m (1 + 4^m slash 2)$ is increasing in $m$.
]

Equality holds for $n = 1$, where $E(2) = 3$; the quotients $E(n + 1) slash E(n)$ of @tab:structure increase from $3$ to $7.84$.
The proportions for the square are among the roots in $[1, infinity)$ of the polynomials $N - D$ of the functions of $cal(F)_n$, by the second statement of @prop:functions, a function and its inverse having the same roots, so that $a(n) <= n E(n)$ by the fifth statement of @prop:reactance.
The argument of @prop:functions-growth does not extend to the square, where a function may have several roots in $[1, infinity)$ or none and different functions may share a root; we do not know whether $a(n + 1) > a(n)$ for every $n$, and @sec:full-side considers the same question for the tilings.

== Rational proportions that need both orientations <sec:rational>

A _dissection of a rectangle into squares_ is a tiling of the rectangle all of whose tiles are squares.
A similar tiling of the unit square of proportion $x$ whose tiles are all wide becomes, when the ordinates are multiplied by $x$, a dissection of the rectangle $[0, 1] times [0, x]$ into squares, and conversely; a tiling whose tiles are all tall is the transpose of one whose tiles are all wide.
So a proportion $x in P_n (1)$ is achieved by $n$ tiles of a single orientation exactly when a rectangle of sides $x$ and $1$ can be dissected into $n$ squares.

By @tab:rational some rational proportions are achievable with $n$ tiles only if both orientations are used, and from ten tiles onwards the search finds exactly three: $n - 4$, $n - 11 slash 2$ and $n - 19 slash 3$.
These are obtained by surrounding the three most elongated rectangles that can be dissected into $n - 4$ squares with a pinwheel.

#proposition[
  The proportion $n - 4$ belongs to $P_n (1)$ for every $n >= 6$, the proportion $n - 11 slash 2$ for every $n >= 7$, and the proportion $n - 19 slash 3$ for every $n >= 8$.
] <prop:three-occur>

#proof[
  Let $m := n - 4$.
  A rectangle of sides $m$ and $1$ is dissected into $m$ squares of side $1$.
  For $m >= 3$, a rectangle of sides $2 m - 3$ and $2$ is dissected into $m - 2$ squares of side $2$ and two of side $1$.
  For $m >= 4$, a rectangle of sides $3 m - 7$ and $3$ is dissected into $m - 3$ squares of side $3$, one of side $2$ and two of side $1$.
  So $m$, $m - 3 slash 2$ and $m - 7 slash 3$ belong to $P_m (1)$ for $m >= 2$, $m >= 3$ and $m >= 4$ respectively, and they exceed $1$.
  By the second statement of @prop:subdivision, they belong to $P_(m + 4) (1)$.
]

That the three rectangles cannot be dissected into $n$ squares is reduced below to three finite statements, of which the first is the following.

#proposition[
  A square cannot be dissected into five squares.
] <prop:five-squares>

#proof[
  Suppose that the unit square is dissected into five squares.
  Each corner of the unit square lies in exactly one of the squares, and no square contains two corners.
  Let $A$, $B$, $C$ and $D$ be the squares at the corners, in order around the unit square from the bottom-left corner, of sides $a$, $b$, $c$ and $d$, and let $Q$ be the fifth square.
  A square that has a segment in common with two sides of the unit square contains a corner or has side $1$, so $Q$ has a segment in common with at most one side, say with none of the bottom, right and top sides.
  Each of these three sides is then covered by its two corner squares, so that $a + b = b + c = c + d = 1$.
  Hence $c = a$ and $d = b$, so that $a + d = 1$, and the left side is covered by $A$ and $D$ as well.
  The squares $A = [0, a]^2$ and $C = [1 - a, 1]^2$ have disjoint interiors, so $a <= 1 slash 2$; similarly $b <= 1 slash 2$.
  So $a = b = 1 slash 2$, the four corner squares fill the unit square, and there is no room for $Q$.
]

The other reductions rest on one identity, which counts the squares of a dissection by integrating over the vertical lines.
Let a rectangle $[0, L] times [0, H]$ be dissected into $k$ squares of sides $s_1, dots, s_k$, and for $u in [0, L]$, not the abscissa of a corner of a square, let $h(u)$ be the sum of the numbers $1 slash s_i$ over the squares that the vertical line of abscissa $u$ crosses.
Since the $i$-th square is crossed for $u$ in an interval of length $s_i$,
$ k = integral_0^L h(u) dif u. $ <eq:reciprocals>
The squares crossed by one line have sides that add up to $H$; if there are $m$ of them, then $h(u) >= m^2 slash H$, by the inequality between the arithmetic and the harmonic mean.

The first use of the identity removes the squares of the largest possible size.

#proposition[
  Let a rectangle $[0, L] times [0, 1]$ be dissected into $n$ squares, $f$ of which have side $1$.
  Then there is a dissection of $[0, L - f] times [0, 1]$ into $n - f$ squares of side less than $1$, and $n - f >= 4 (L - f)$.
] <prop:unit-squares>

#proof[
  A square of side $1$ occupies a full column, so the squares of side $1$ cut the rectangle into rectangles of height $1$, each of which is dissected by the squares that it contains.
  Translating these rectangles so that they are adjacent gives the dissection.
  In it every vertical line crosses at least two squares, so that $h >= 4$, and @eq:reciprocals gives the inequality.
]

The second finite statement is obtained by measuring how far the function $h$ exceeds its least possible value.

#proposition[
  A rectangle of sides $3$ and $2$ cannot be dissected into seven squares of side less than $2$.
] <prop:seven-squares>

#proof[
  Suppose that there is such a dissection, take $L = 3$ and $H = 2$, and let $d(u) := h(u) - 2$.
  Every line crosses at least two squares, so that $d >= 0$, and $integral_0^3 d(u) dif u = 1$ by @eq:reciprocals.
  A line is of _type a_ if it crosses two squares of side $1$, where $d = 0$; of _type b_ if it crosses two squares of sides $sigma > 1$ and $2 - sigma$, where $d = delta(sigma) := 2 slash (sigma (2 - sigma)) - 2$; and of _type c_ if it crosses at least three squares, where $d >= 9 slash 2 - 2 = 5 slash 2$.
  The lines of type c therefore have total length at most $2 slash 5$.
  Call a square _big_ if its side exceeds $1$.
  No line crosses two big squares, so the horizontal extents of the big squares do not overlap, and there are at most two of them.
  A line of type a crosses a square of side $1$ that touches the bottom side; the extent of such a square has length $1$ and does not overlap the extent of a big square.
  Put $eta(sigma) := sigma delta(sigma) = 2 (sigma - 1)^2 slash (2 - sigma)$.
  There are three cases.

  _No big square._
  Every line is of type a or c, so the lines of type a have total length at least $13 slash 5$.
  Each crosses two squares of side $1$, and a square of side $1$ is crossed over a length $1$, so there are at least $26 slash 5$, hence six, squares of side $1$.
  Their area is $6$, which leaves no room for the seventh square.

  _One big square_, of side $sigma$.
  The lines through it are of type b or c, so that $1 >= sigma min(delta(sigma), 5 slash 2)$; as $sigma > 1$ this gives $eta(sigma) <= 1$, that is, $sigma <= 3 slash 2$.
  The lines outside its extent are of type a or c, so those of type a have total length at least $3 - sigma - 2 slash 5 >= 11 slash 10$.
  But the complement of the extent consists of at most two intervals of total length $3 - sigma < 2$, so it contains the extent of at most one square of side $1$ touching the bottom side, and the lines of type a have total length at most $1$.

  _Two big squares_, of sides $sigma_1$ and $sigma_2$.
  The complement of their extents has length $3 - sigma_1 - sigma_2 < 1$, so it contains no line of type a, and all its lines are of type c.
  Hence
  $ 1 >= sum_j sigma_j min(delta(sigma_j), 5 slash 2) + 5 / 2 (3 - sigma_1 - sigma_2). $
  With $v := 2 - sigma$ we have $eta(sigma) - (5 slash 2) sigma = 2 slash v + (9 slash 2) v - 9 >= -3$, with equality at $v = 2 slash 3$; so $sigma min(delta(sigma), 5 slash 2) >= (5 slash 2) sigma - 3$ in all cases.
  The right-hand side of the inequality displayed is therefore at least $15 slash 2 - 6 = 3 slash 2$, a contradiction.
]

The third finite statement needs a longer analysis, by the number of squares that touch neither the top nor the bottom side.

#proposition[
  A rectangle of sides $5$ and $3$ cannot be dissected into eight squares of side less than $3$.
] <prop:eight-squares>

#proof[
  Take $L = 5$ and $H = 3$, and suppose that such a dissection exists.
  Call a square _lower_ if it touches the bottom side, _upper_ if it touches the top side, and _middle_ otherwise; no square is both lower and upper.
  A vertical line that avoids the corners crosses one lower square, of side $sigma$, one upper square, of side $theta$, and possibly middle squares, of sides $c_i$; and $1 slash sigma + 1 slash theta >= 4 slash (sigma + theta) >= 4 slash 3$.
  By @eq:reciprocals, $8 >= 5 dot.op 4 slash 3 + integral_0^5 sum_i 1 slash c_i dif u$, and the integral is the number of middle squares, so there is at most one.
  A _cut_ is a vertical line, other than the two vertical sides of the rectangle, that crosses the interior of no square; the cuts divide the rectangle into _blocks_, each of which is dissected by the squares that it contains.

  _Blocks without a middle square._
  Every line crosses a lower and an upper square with $sigma + theta = 3$.
  Where the lower square changes, inside the block, the upper square does not, as the line is not a cut; so consecutive lower squares have the same side, and likewise the upper ones.
  The block thus consists of $a$ lower squares of side $sigma$ and $b$ upper squares of side $3 - sigma$ with $a sigma = b (3 - sigma)$, and $a$ and $b$ are coprime, as otherwise there would be a cut inside.
  It has $a + b$ squares and width $3 a b slash (a + b)$: the widths are $3 slash 2$ for two squares, $2$ for three, $9 slash 4$ for four, $12 slash 5$ or $18 slash 5$ for five, $5 slash 2$ for six, $18 slash 7$, $30 slash 7$ or $36 slash 7$ for seven, and $21 slash 8$ or $45 slash 8$ for eight.

  _No middle square._
  The numbers of squares of the blocks form a partition of $8$ into parts at least $2$, and the widths add up to $5$.
  The partitions $8$; $6 + 2$; $5 + 3$; $4 + 4$; $4 + 2 + 2$; $3 + 3 + 2$; $2 + 2 + 2 + 2$ give the total widths $21 slash 8$ or $45 slash 8$; $4$; $22 slash 5$ or $28 slash 5$; $9 slash 2$; $21 slash 4$; $11 slash 2$; $6$, none of which is $5$.

  _One middle square_ $Q$, of side $c$.
  The lines through $Q$ cross three squares, so that $h >= 3$ on a length $c$, and @eq:reciprocals gives $8 >= 20 slash 3 + (5 slash 3) c$, that is, $c <= 4 slash 5$.
  On these lines the lower squares have their top at the bottom of $Q$ and the upper squares their bottom at its top; so the lower squares below $Q$ have a common side $sigma$, the upper squares above $Q$ a common side $theta^*$, and $sigma + c + theta^* = 3$.
  Let the block that contains $Q$ have width $omega$ and $k$ squares, and let it be $[0, omega] times [0, 3]$, with $Q$ above the interval $[u_Q, u_Q + c]$.
  The other blocks have no middle square, so their numbers of squares form a partition of $8 - k$ into parts at least $2$.
  It is shown below that $k >= 4$; hence $(k, omega)$ is one of $(8, 5)$, $(6, 7 slash 2)$, $(5, 3)$, $(4, 11 slash 4)$ and $(4, 2)$.

  Suppose that $u_Q > 0$.
  To the left of $Q$ the lines cross two squares, and as before all the lower squares there have one side $sigma_L$ and all the upper squares the side $3 - sigma_L$.
  The line of abscissa $u_Q$ is not a cut, so it crosses the interior of a lower or of an upper square.
  If it is a lower one, then $sigma_L = sigma$; if it is an upper one, then $3 - sigma_L = theta^*$; these are mutually exclusive because $c > 0$.
  So exactly one of the two kinds of square straddles the line of abscissa $u_Q$, and the squares of the other kind end there.
  The same holds at $u_Q + c$ if $u_Q + c < omega$.
  Up to the reflections of the rectangle in its two axes, four cases remain.

  _Case (i): $u_Q = 0$ and $u_Q + c = omega$._
  Then $c = a sigma = b theta^*$ with integers $a, b >= 1$, so that $3 = c (1 + 1 slash a + 1 slash b) <= 3 c$, contrary to $c <= 4 slash 5$.

  _Case (ii): $u_Q = 0$, and a lower square straddles the line of abscissa $c$._
  All $p$ lower squares have side $sigma = omega slash p$; $a >= 1$ upper squares lie above $Q$; and $b >= 1$ upper squares of side $3 - sigma$ fill the rest, so that $c = omega - b (3 - sigma) = omega (1 + b slash p) - 3 b$, with $k = p + a + b + 1$ and $p + b <= k - 2$.
  For $k = 4$: $c = 2 omega - 3 >= 1$.
  For $(k, omega) = (5, 3)$: $c = 3 - 3 b (p - 1) slash p >= 3 slash 2$, as $p + b <= 3$.
  For $(6, 7 slash 2)$: $c = 7 slash 2 + b (7 slash (2 p) - 3)$, which for $p + b <= 4$ is at least $1$.
  For $(8, 5)$: $c = 5 - b (3 - 5 slash p)$, which for $p + b <= 6$ is at least $1$.
  All contradict $c <= 4 slash 5$.

  _Case (iii): $0 < u_Q$, $u_Q + c < omega$, and lower squares straddle both lines._
  All $p$ lower squares have side $sigma = omega slash p$; $a >= 1$ upper squares lie above $Q$, and $t >= 2$ upper squares of side $3 - sigma$ lie to its left and right, so that $c = omega (1 + t slash p) - 3 t$, with $k = p + a + t + 1$ and $p + t <= k - 2$.
  For $(5, 3)$: $c = 3$.
  For $(6, 7 slash 2)$: $c >= 1$.
  For $(8, 5)$: $c = 5 + t (5 slash p - 3)$, which for $p + t <= 6$ is at least $1$.
  All contradict $c <= 4 slash 5$.

  _Case (iv): $0 < u_Q$, $u_Q + c < omega$, a lower square straddles the line of abscissa $u_Q$ and an upper square that of abscissa $u_Q + c$._
  From the left, there are $a$ lower squares of side $sigma$, ending at $u_Q + c$, then $b$ lower squares of side $3 - theta^* = sigma + c$; and $a'$ upper squares of side $3 - sigma$, ending at $u_Q$, then $b'$ upper squares of side $theta^* = 3 - sigma - c$.
  So $k = a + b + a' + b' + 1$ and
  $ (a + b) sigma + b c = omega, quad (a' + b') (3 - sigma) - b' c = omega, quad a sigma - c = a' (3 - sigma). $
  The rotation of the rectangle by a half-turn exchanges $(a, b, a', b')$ with $(b', a', b, a)$.
  For $(5, 3)$, all four numbers are $1$, and the first and third equations give $c = 0$.
  For $(6, 7 slash 2)$, up to the half-turn $(a, b, a', b')$ is $(2, 1, 1, 1)$ or $(1, 2, 1, 1)$: the first and third equations give $(sigma, c) = (13 slash 12, 1 slash 4)$, which violates the second, and $(19 slash 14, -2 slash 7)$.
  For $(8, 5)$, $a + b + a' + b' = 7$; up to the half-turn $a + b <= 3$.
  If $a + b = 2$, the first equation gives $sigma >= (5 - 4 slash 5) slash 2 > 2$ and the second $5 (3 - sigma) > 5$, a contradiction.
  If $a + b = 3$, the first and third equations give, for $(a, b; a', b')$ equal to $(1, 2; 1, 3)$, $(1, 2; 2, 2)$, $(1, 2; 3, 1)$, $(2, 1; 1, 3)$, $(2, 1; 2, 2)$ and $(2, 1; 3, 1)$, the values $(sigma, c) = (11 slash 7, 1 slash 7)$, $(17 slash 9, -1 slash 3)$, $(23 slash 11, -7 slash 11)$, $(4 slash 3, 1)$, $(11 slash 7, 2 slash 7)$ and $(7 slash 4, -1 slash 4)$.
  Three have $c < 0$; for the others the left-hand side of the second equation is $37 slash 7$, $11 slash 3$ and $36 slash 7$, not $5$.

  In the cases (ii) to (iv) the block has at least four squares, as was used above.
]

Independently of this proof, the search finds that a rectangle of sides $5$ and $3$ cannot be dissected into eight squares of any side lengths: restricted to tiles of a single orientation, it does not report the proportion $1$ for eight tiles in that rectangle, and the run is certified.

The three finite statements give the three impossibilities for every $n$.

#proposition[
  + For $n >= 5$, a rectangle of sides $n - 4$ and $1$ cannot be dissected into $n$ squares.
  + For $n >= 6$, a rectangle of sides $n - 11 slash 2$ and $1$ cannot be dissected into $n$ squares.
  + For $n >= 7$, a rectangle of sides $n - 19 slash 3$ and $1$ cannot be dissected into $n$ squares.
] <prop:no-squares>

#proof[
  Suppose that a rectangle of sides $L$ and $1$ is dissected into $n$ squares, and apply @prop:unit-squares: there is a dissection of a rectangle of sides $ell$ and $1$ into $k$ squares of side less than $1$, where $ell := L - f$ and $k := n - f$, so that $k - ell = n - L$, and $k >= 4 ell$.

  For the first statement, $k - ell = 4$ and $ell$ is an integer, so that $4 ell <= ell + 4$ gives $ell <= 1$.
  If $ell = 0$ then $k = 0$, which contradicts $k - ell = 4$.
  If $ell = 1$ then $k = 5$, which contradicts @prop:five-squares.

  For the second statement, $k = ell + 11 slash 2$, so that $ell <= 11 slash 6$, and $ell - 1 slash 2$ is an integer: $ell = 1 slash 2$ or $ell = 3 slash 2$.
  If $ell = 1 slash 2$ then $k = 6$, and a rectangle of sides $2$ and $1$ would be dissected into six squares, contrary to the first statement for $n = 6$.
  If $ell = 3 slash 2$ then $k = 7$, and a rectangle of sides $3$ and $2$ would be dissected into seven squares of side less than $2$, contrary to @prop:seven-squares.

  For the third statement, $k = ell + 19 slash 3$, so that $ell <= 19 slash 9$, and $ell - 2 slash 3$ is an integer: $ell = 2 slash 3$ or $ell = 5 slash 3$.
  If $ell = 2 slash 3$ then $k = 7$, and a rectangle of sides $3$ and $2$ would be dissected into seven squares, contrary to the second statement for $n = 7$.
  If $ell = 5 slash 3$ then $k = 8$, and a rectangle of sides $5$ and $3$ would be dissected into eight squares of side less than $3$, contrary to @prop:eight-squares.
]

So, for $n >= 8$, the proportions $n - 4$, $n - 11 slash 2$ and $n - 19 slash 3$ belong to $P_n (1)$ and are achieved with $n$ tiles only by tilings with both orientations; the same holds for $n - 4$ from $n = 6$ and for $n - 11 slash 2$ from $n = 7$.

The same argument shows that, for $m >= 4$, the numbers $m$, $m - 3 slash 2$ and $m - 7 slash 3$ are the three largest $L$ for which a rectangle of sides $L$ and $1$ can be dissected into $m$ squares, which is the sense in which the rectangles used in the proof of @prop:three-occur are the most elongated.
Indeed, in the notation of the proof of @prop:no-squares with $n = m$, if $0 < m - L < 7 slash 3$ then $3 ell <= k - ell = m - L$ gives $ell < 7 slash 9$, and $k = ell + (m - L) < 28 slash 9$, so that $k <= 3$.
Two squares of side less than $1$ dissect a rectangle of sides $ell$ and $1$ only for $ell = 1 slash 2$, which gives $m - L = 3 slash 2$.
Three such squares do so only for $ell = 1 slash 3$ and $ell = 2 slash 3$: one of them contains a left and a right corner, so it has side $ell$, and the other two dissect a rectangle of sides $ell$ and $1 - ell$, one of which is then twice the other.
These give $m - L = 8 slash 3$ and $7 slash 3$.

#conjecture[
  For every $n >= 10$, the rational proportions in $P_n (1)$ that are not achievable with $n$ tiles of a single orientation are exactly $n - 4$, $n - 11 slash 2$ and $n - 19 slash 3$.
] <conj:exceptional>

The conjecture holds for $10 <= n <= 13$; it was formulated from the cases $n = 10$ and $n = 11$ and then confirmed for $12$ and $13$.
The last column of @tab:structure extends the eight known terms of A210517 @oeisA210517 by five; a sixth, $155656$ for $n = 14$, was also computed.

There are further exceptions for small $n$.
For $6 <= n <= 9$, the rational proportions in $P_n (1)$ that are not achieved by $n$ tiles of a single orientation are, according to the search, $5 slash 3$ and $2$ for six tiles; $3 slash 2$ and $3$ for seven; $5 slash 3$, $5 slash 2$ and $4$ for eight; and $8 slash 3$, $16 slash 5$, $7 slash 2$ and $5$ for nine; the first three lists are those of @tab:rational.
@prop:three-occur and @prop:no-squares account for all of them except two, since $n - 11 slash 2 > 1$ requires $n >= 7$ and $n - 19 slash 3 > 1$ requires $n >= 8$.
The other two are sporadic, and come from pinwheels whose central rectangle is not a square.

#example[
  @fig:sporadic shows the two sporadic tilings.
  For $5 slash 3 in P_6 (1)$, in a square of side $105$: a wide tile of width $75$ and height $45$ at the bottom-left corner, a tall tile of width $30$ and height $50$ at the bottom-right corner, a tall tile of width $33$ and height $55$ at the top-right corner, two tall tiles of width $36$ and height $60$ side by side at the top-left corner, and a tall tile of width $3$ and height $5$ in the centre.
  For $16 slash 5 in P_9 (1)$, in a square of side $3040$: a wide tile of width $2560$ and height $800$ at the bottom-left corner, a tall tile of width $480$ and height $1536$ at the bottom-right corner, two tall tiles of width $470$ and height $1504$ at the top-right corner, three tall tiles of width $700$ and height $2240$ at the top-left corner, and two tall tiles of width $230$ and height $736$ in the centre.
] <ex:sporadic>

#figure(
  image("figures/sporadic.svg", width: 58%),
  caption: [The tilings of @ex:sporadic, of proportion $5 slash 3$ with six tiles and of proportion $16 slash 5$ with nine, drawn from their records.],
) <fig:sporadic>

That rectangles of sides $5$ and $3$, and of sides $16$ and $5$, cannot be dissected into six and into nine squares respectively is a result of the search, and is not proved here.
Why no such sporadic proportion occurs for $10 <= n <= 13$ is not explained.
For @conj:exceptional we know of no argument that would bound the rational proportions of tilings with both orientations, and of no general construction that adds four squares to a dissection into squares, which is what would be needed to achieve with $n$ squares the remaining rational elements of $P_(n - 4) (1)$.

== Guillotine tilings <sec:guillotine>

For guillotine tilings the functions can be described directly, and are those of the series–parallel circuits.

#definition(name: [guillotine tilings and their functions])[
  A tiling is _guillotine_ if it consists of a single tile, or of two guillotine tilings of the two rectangles into which a segment, parallel to a side and joining two opposite sides, divides its main rectangle.
  Let $cal(G)_1 := {x, 1 slash x}$, and for $n >= 2$ let $cal(G)_n$ be the set of rational functions $A + B$ and $(A^(-1) + B^(-1))^(-1)$ with $A in cal(G)_j$, $B in cal(G)_(n - j)$ and $1 <= j < n$.
  Let $g(n)$ be the number of those $x in P_n (1)$ for which the unit square has a similar guillotine tiling of proportion $x$ with $n$ tiles.
  Let $sigma_n$ be the number of expressions that define the elements of $cal(G)_n$, considered up to the commutativity and the associativity of the two operations; these are the series–parallel networks with $n$ edges of two kinds.
] <def:guillotine>

By induction on $n$, the ratio of the width to the height of the main rectangle of a similar guillotine tiling of proportion $x$ with $n$ tiles, with an orientation vector, is $F(x)$ for some $F in cal(G)_n$: the function is $x$ for a wide tile and $1 slash x$ for a tall one, two tilings side by side give the sum, and two tilings one above the other give the other operation.
Conversely every $F in cal(G)_n$ and every $x > 0$ arise in this way, from a tiling whose tiles have height $x^(plus.minus 1)$ times their width.
The numbers $sigma_n$ begin with $2, 6, 20, 80, 340, 1570, 7540$.
The sequence A338781 of the OEIS @oeisA338781 is half the largest number of distinct resistances obtainable from $n$ resistors of two kinds by series and parallel combinations.

#proposition[
  Let $n >= 1$.
  + The set $cal(G)_n$ is closed under inversion, $F != 1 slash F$ for every $F in cal(G)_n$, and $abs(cal(G)_n) slash 2$ is the $n$-th term of A338781.
  + $g(n) <= n abs(cal(G)_n) slash 2 <= n sigma_n slash 2$.
] <prop:guillotine>

#proof[
  For the first statement, $1 slash (A + B)$ is obtained from $1 slash A$ and $1 slash B$ by the second operation, and conversely, so that $cal(G)_n$ is closed under inversion by induction.
  Every element of $cal(G)_n$ is the inverse of the impedance function of the network of a tiling, so that $F != 1 slash F$ by the first statement of @prop:reactance.
  The resistance of a series–parallel circuit of resistors of values $u$ and $v$ is a rational function $rho(u, v)$, homogeneous of degree one, so that $rho(u, v) = sqrt(u v) thin rho(sqrt(u slash v), sqrt(v slash u))$.
  Hence $rho$ is determined by $F(x) = rho(x, 1 slash x)$, and $rho |-> F$ is a bijection from the set of these functions to $cal(G)_n$; the largest number of resistances is the number of distinct functions $rho$, attained when $u$ and $v$ are algebraically independent.
  Under this bijection $1 slash F$ corresponds to $u v slash rho(u, v) = 1 slash rho(1 slash v, 1 slash u)$, the resistance of the circuit with series and parallel exchanged and the two kinds of resistor swapped.

  For the second statement, a proportion of a similar guillotine tiling of the square is a solution $x >= 1$ of $F(x) = 1$ with $F in cal(G)_n$; the functions $F$ and $1 slash F$ have the same solutions, and there are at most $n$ of them, by the fifth statement of @prop:reactance.
  The map from expressions to functions is onto $cal(G)_n$.
]

In particular the resistances of the first statement come in pairs, exchanged by swapping the two kinds of resistor and exchanging series with parallel.
A comment in the entry A338781 presents this as unproved, but the entry also links to a note by Einstein containing a proof that the largest number of resistances is even, so the pairing is not new.

The proof of @prop:wide-full applies to guillotine tilings, with $cal(F)_n$ replaced by $cal(G)_n$; its fourth step is then immediate, since a guillotine tiling exists for every $x > 0$.
So, for $w$ large enough, the number of proportions of similar guillotine tilings of $[0, w] times [0, 1]$ with $n$ tiles is $abs(cal(G)_n) slash 2$.

A series–parallel network is a single edge, or a multiset of at least two networks joined in series, none of them itself a series composition, or the same in parallel.
So the numbers $sigma_n$ satisfy
$
  product_(j >= 1) (1 - z^j)^(-beta_j) = 1 + sum_(n >= 1) sigma_n z^n, quad beta_1 = 2, quad beta_j = sigma_j slash 2 quad "for" j >= 2.
$
The quotients $sigma_(n + 1) slash sigma_n$, corrected by the factor $(1 - 3 slash (2 n + 2))^(-1)$, are $6.15881$, $6.15887$ and $6.15889$ at $n = 100$, $200$ and $399$.
So the growth constant of $g(n)$ is at most that of $sigma_n$, which is numerically $6.1589$.
That $sigma_n$ grows as a constant times $gamma^n n^(-3 slash 2)$ for some $gamma$ is the usual behaviour of such equations, and is not proved here; the value of the constant is known only numerically.

The number of proportions achievable by guillotine tilings is a decreasing share of the total in @tab:structure: $90$ per cent for six tiles, and $13.5$ per cent for twelve.

#conjecture[
  The proportion of the elements of $P_n (1)$ that are achievable by a guillotine tiling with $n$ tiles tends to zero as $n$ tends to infinity.
] <conj:guillotine>

@conj:guillotine is supported by the values for $n <= 12$.

== Tilings with a tile along a side <sec:full-side>

We do not know whether $t(n + 1) >= t(n)$ for every $n$, nor whether $a(n + 1) > a(n)$.
This section gives a lower bound for $t(n + 1)$ in terms of a number of networks with $n$ edges, which in the range computed exceeds $t(n)$.
The tilings that it counts consist of a tiling of a rectangle with $n$ tiles and of one more tile along a whole side of the square.
It first shows that a tiling can be recovered from its network, and conversely.

#definition(name: [regular point])[
  Two plane networks are _isomorphic_ if there are bijections between their vertices and between their edges that preserve the ends of the edges, the poles, and the cyclic order of the edges of $G^+$ around each vertex, the edge $e_0$ of one corresponding to that of the other and its position in the cyclic orders at the poles being part of the data.
  A _pair_ with $n$ edges is a plane network with $n$ edges with an orientation vector, and two pairs are isomorphic if there is an isomorphism of their plane networks that preserves the orientations.
  Let $frak(N)$ be a plane network with positive real resistances, and let $(phi, i)$ be a flow of positive value, with real potential, in which no current vanishes; direct the edges so that the currents are positive, and let $rct(e)$ be the rectangles of @prop:bsst.
  For a vertex $v$, let $S_v$ be the union of the top sides of the rectangles $rct(e)$ with $e^- = v$ and of the bottom sides of the rectangles $rct(e)$ with $e^+ = v$.
  The flow is _regular_ if the sets $S_v$ are pairwise disjoint.
  For a pair $(frak(N), epsilon)$, a number $x > 0$ is a _regular point_ if no current of the flow of value $1$ for the resistances $x^(epsilon_e)$ vanishes and that flow is regular.
] <def:regular-point>

The faces of a connected plane graph, with the faces to the left and to the right of each edge, are determined by the cyclic orders of the edges around its vertices.
An isomorphism of plane networks therefore maps a flow to a flow, the function $psi$ of @prop:face-potential to that of the image, and the rectangles $rct(e)$ to the same rectangles up to a translation; so regularity, and the tiling of @prop:bsst, depend only on the isomorphism class.

#proposition[
  Let $frak(N)$ be a plane network with positive real resistances, and let $(phi, i)$ be a flow of value $I > 0$, with real potential, in which no current vanishes, with the edges directed so that the currents are positive.
  + At every vertex other than the poles, the edges that leave it are consecutive in the cyclic order around it.
  + For every vertex $v$, the set $S_v$ is a horizontal segment at height $phi(v)$, and it is the union of the top sides of the rectangles of the edges that leave $v$, as well as the union of the bottom sides of the rectangles of the edges that enter $v$, when $v$ has such edges. In counter-clockwise order around $v$, the edges that leave $v$ come in the order of their rectangles from left to right, and are followed by the edges that enter $v$ in the order of their rectangles from right to left. The sets $S_s$ and $S_t$ are the top and the bottom side of the main rectangle.
  + If $v != w$ and $S_v$ meets $S_w$, then they meet in a single point, which is a corner of four tiles.
] <prop:segments>

#proof[
  By the proof of @prop:bsst, the potential decreases strictly along every edge, every vertex other than the poles has an edge that enters it and one that leaves it, from every vertex a directed path leads to $t$, and a path that follows the edges backwards leads to $s$.

  For the first statement, suppose that edges $a$, $b$, $c$, $d$ occur in this cyclic order around a vertex $v$ other than the poles, with $a$ and $c$ leaving $v$ and $b$ and $d$ entering it.
  Take directed paths from $v$ to $t$ that begin with $a$ and with $c$, and let $z$ be the first vertex after $v$ on the first path that lies on the second.
  The parts of the two paths from $v$ to $z$ form a closed curve $C$ all of whose vertices other than $v$ have potential smaller than $phi(v)$.
  Since $a$ and $c$ separate $b$ from $d$ in the cyclic order around $v$, the edges $b$ and $d$ begin in different components of the complement of $C$, by the Jordan curve theorem.
  The paths from $v$ that follow the edges backwards and begin with $b$ and with $d$ lead to $s$ through vertices of potential larger than $phi(v)$, so they meet $C$ only at $v$; hence $s$, which is not on $C$, lies in both components, which is absurd.

  For the second, let $v$ be a vertex other than the poles and let $e_1, dots, e_k$ be the edges that leave it, in counter-clockwise order, followed by the edges $e'_1, dots, e'_m$ that enter it.
  The face that follows a leaving edge $e$ counter-clockwise around its tail is $lft(e)$, and the one that precedes it is $rgt(e)$; for an entering edge the face that follows it around its head is $rgt(e)$ and the one that precedes it is $lft(e)$.
  Hence $lft(e_j) = rgt(e_(j + 1))$, so that the top sides $[psi(rgt(e_j)), psi(lft(e_j))] times {phi(v)}$ of the rectangles of the leaving edges follow one another from left to right and their union is $[psi(rgt(e_1)), psi(lft(e_k))] times {phi(v)}$.
  Similarly $lft(e'_1) = lft(e_k)$, $rgt(e'_j) = lft(e'_(j + 1))$ and $rgt(e'_m) = rgt(e_1)$, so that the bottom sides of the rectangles of the entering edges follow one another from right to left and have the same union.
  At $s$ the edge $e_0$ of $G^+$ is the only one that enters, with $lft(e_0) = f_R$ and $rgt(e_0) = f_L$, and the same computation shows that the top sides of the rectangles of the edges that leave $s$ cover $[psi(f_L), psi(f_R)] times {phi(s)}$; likewise at $t$.

  For the third, $S_v$ and $S_w$ are at the same height, so neither $v$ nor $w$ is a pole, the potential of every other vertex lying strictly between those of the poles.
  Suppose that the two segments have a common point $p$ that is not an end of both.
  Both have positive length, so they then have a common point $q$ whose abscissa is not that of any corner of a tile; the points just above $q$ lie in the interior of a single tile $rct(e)$.
  By the second statement $q$ lies on the bottom side of the rectangle of an edge that enters $v$, which is then $rct(e)$, so that $e^+ = v$; likewise $e^+ = w$, which is absurd.
  So the segments have only an end $p$ in common, the right end of $S_v$ and the left end of $S_w$, say.
  By the second statement, the last rectangle above $S_v$, the first above $S_w$, the last below $S_v$ and the first below $S_w$ are four tiles with a corner at $p$; they are distinct, since their edges differ in their heads or in their tails and no edge joins $v$ and $w$, which have the same potential.
]

#proposition[
  + Let $frak(N)$ be a plane network with positive real resistances and a regular flow, and let $tau$ be the tiling of @prop:bsst. Then $e |-> rct(e)$ induces an isomorphism of plane networks from $frak(N)$ to $frak(N)(tau)$, under which the resistance of $e$ is that of the tile $rct(e)$.
  + Let $tau$ be a tiling of a rectangle. For the plane network $frak(N)(tau)$, with the resistances and the flow of @prop:tiling-network, the rectangles of @prop:bsst are the tiles of $tau$, up to a translation, and the flow is regular.
] <prop:reconstruction>

#proof[
  For the first statement, every top side and every bottom side of a tile lies in one of the sets $S_v$, which form a finite family of pairwise disjoint segments; so these sets are the connected components of the union of the top and bottom sides of the tiles, that is, the vertices of $frak(N)(tau)$.
  The tile $rct(e)$ has its top side in $S_(e^-)$ and its bottom side in $S_(e^+)$, and $S_s$ and $S_t$ are the top and bottom sides of the main rectangle, by @prop:segments.
  In the embedding of $frak(N)(tau)$ given in the proof of @prop:tiling-network, the edges around a component are, counter-clockwise, the tiles below it from left to right followed by the tiles above it from right to left; at each pole the edge added between the poles occupies the only gap, between the last and the first edge of the network. This is the order given by @prop:segments.

  For the second, draw $frak(N)(tau)$ as in the proof of @prop:tiling-network, with each tile represented by the vertical segment through its centre and each component contracted to a point; contracting the components does not change the faces, so we describe them before the contraction.
  The centre segment cuts the interior of a tile into a left and a right half.
  A point of the main rectangle that lies on no component and on no centre segment is in a half of a tile, or on a vertical side of a tile.
  The left halves of the tiles along the left side of the main rectangle lie in $f_L$ and the right halves of the tiles along its right side in $f_R$, and these two faces are distinct, since $e_0$ separates them.
  Two other halves lie in the same face exactly if they are joined by a chain of halves in which consecutive ones share such a point of a vertical side, and then the left side of the tile of a left half, or the right side of the tile of a right half, is at the same abscissa along the chain.
  Let $psi_0 (f)$ be this common abscissa for a face $f$ inside the main rectangle, and let $psi_0$ be the abscissa of the left side of the main rectangle on the face to its left and that of the right side on the face to its right; these are the two faces at $e_0$.
  For the edge $e$ of a tile $T$, directed downwards, $lft(e)$ contains the right half of $T$ and $rgt(e)$ its left half, so that $psi_0 (lft(e)) - psi_0 (rgt(e))$ is the width of $T$, which is the current in $e$; and $psi_0 (f_R) - psi_0 (f_L)$ is the width of the main rectangle, which is the value of the flow.
  By the uniqueness in @prop:face-potential, $psi_0$ differs from $psi$ by a constant, and the potential is the height by @prop:tiling-network; so $rct(e)$ is $T$, up to a translation.
  The sets $S_v$ are then contained in distinct components, and so are disjoint.
]

Besides the three facts named before @prop:bsst, the proofs use that the contraction of the components does not change the faces of the drawing, and that the faces of a connected plane graph are determined by the cyclic orders around its vertices.
By the third statement of @prop:segments, a flow is regular whenever no four tiles of its tiling meet at a point.

#proposition[
  Let $n >= 1$, and let $s(n)$ be the number of tilings of the unit square by $n$ squares.
  + The similar tilings of the unit square with $n$ tiles and proportion $x > 1$ correspond bijectively to the triples $(frak(N), epsilon, x)$ of a pair with $n$ edges, taken up to isomorphism, and of a regular point $x > 1$ of it with $Z_(frak(N), epsilon) (x) = 1$. Hence $t(n) - s(n)$ is the number of these triples.
  + Every pair $(frak(N), epsilon)$ with impedance function $F$ has a _full-side root_: a number $x > 1$ with $F(x) = 1 - 1 slash x$, if $F$ tends to $0$ at infinity, or with $F(x) = x slash (x - 1)$, if $F$ tends to $infinity$.
  + Let $g(n)$ be the number of isomorphism classes of pairs with $n$ edges that have a full-side root which is a regular point. Then $t(n + 1) >= g(n)$.
] <prop:full-side>

#proof[
  For the first statement, a tiling $tau$ of proportion $x > 1$ has exactly one orientation vector $epsilon$, and $x$ is a regular point of $(frak(N)(tau), epsilon)$ at which the impedance function is $1$, by @prop:functions and the second statement of @prop:reconstruction, which also shows that $tau$ is determined by the pair and $x$.
  Conversely, at a regular point $x > 1$ of a pair $(frak(N), epsilon)$ with value $1$, the tiling $tau$ of @prop:bsst for the flow of value $1$ is a similar tiling of the unit square of proportion $x$, with orientation vector $epsilon$, and the pair is isomorphic to $(frak(N)(tau), epsilon)$ by the first statement of @prop:reconstruction.

  For the second, $F(1)$ is a positive real number, by @prop:reactance.
  The function $1 - 1 slash x$ is $0$ at $1$ and tends to $1$ at infinity, so that $F(x) - 1 + 1 slash x$ is positive at $1$ and negative for large $x$ if $F$ tends to $0$; the function $x slash (x - 1)$ tends to $infinity$ at $1$ from the right and to $1$ at infinity, so that $F(x) - x slash (x - 1)$ is negative near $1$ and positive for large $x$ if $F$ tends to $infinity$.
  By the fifth statement of @prop:reactance one of the two cases holds, and the intermediate value theorem gives the root.

  For the third, let $x > 1$ be a regular full-side root of a pair $(frak(N), epsilon)$, and let $tau$ be the tiling of @prop:bsst for the flow of value $1$; it is a similar tiling of proportion $x$ of a rectangle of width $1$ and height $F(x)$.
  If $F(x) = 1 - 1 slash x$, adding a tile of width $1$ and height $1 slash x$ above $tau$ gives a similar tiling of the unit square with $n + 1$ tiles, with a tile along the top side.
  If $F(x) = x slash (x - 1)$, the tiling $tau$ scaled by $(x - 1) slash x$ has width $(x - 1) slash x$ and height $1$, and adding a tile of width $1 slash x$ and height $1$ to its left gives a similar tiling of the unit square with $n + 1$ tiles, with a tile along the left side.
  A tiling of the unit square with at least two tiles does not have both a tile along the top side and a tile along the left side, since their interiors would meet.
  So the tiling obtained determines which case holds; it determines $x$, which is its proportion, and $tau$, by removing the tile along the side; and $tau$ determines the pair up to isomorphism, as in the first statement.
  Choosing one regular full-side root for each class thus gives $g(n)$ distinct tilings.
]

The first statement gives a way of counting the tilings that is independent of the search described in @sec:solving: a plane network in which no current vanishes identically has a non-separable graph $G^+$, since a part of the network that is attached to the rest at a single vertex $u$ and contains no pole carries no current: making the potential equal to $phi(u)$ on that part gives a flow of the same value, which is the flow by the uniqueness in @prop:flow; and when a vertex $u$ of $G^+$ is removed some component contains no pole, since the poles are joined by $e_0$ unless $u$ is one of them.
So it suffices to go through the non-separable planar maps with $n + 1$ edges, rooted at $e_0$ directed from $t$ to $s$ with a fixed side, and for each of them and each orientation vector to find the regular points $x > 1$ with value $1$ among the roots of a polynomial; the tilings by squares are counted in the same way, as the plane networks with unit resistances, impedance $1$ and a regular flow.
We carried this out in floating-point arithmetic for $n <= 9$, and it reproduces the values of $t(n)$ in @tab:tbc.
The same computation gives $g(n)$.

#conjecture[
  For every $n >= 1$, $g(n) >= t(n)$.
] <conj:full-side>

By the third statement of @prop:full-side, @conj:full-side implies that $t(n + 1) >= t(n)$ for every $n$.
It holds for $n <= 10$. For $n <= 9$, according to this computation in floating-point arithmetic, $g(1) = 2$, $g(2) = 8$ and $g(3) = 48$, and $g(n)$ is $346$, $2852$, $25380$, $240608$, $2382684$ and $24415502$ for $n = 4, dots, 9$, between $3.35$ and $3.89$ times $t(n)$.
The quotient $t(n) slash g(n)$ is $0.257$, $0.291$, $0.287$, $0.293$, $0.295$ and $0.298$ for $n = 4, dots, 9$; it increases slowly from six tiles onwards, and the values do not show whether it remains below $1$.
A second computation, in integer arithmetic, certifies regular full-side roots by an exact change of sign on a small interval on which the potentials of the vertices are shown to be pairwise distinct; it certifies $24202856$ pairs for nine tiles, and for ten tiles $77189138$ pairs among the first $80445440$ examined, which exceeds $t(10) = 77188146$.

The inequality does not hold for each network separately.
Let $frak(N)$ be ten blocks in series, each of nine edges in parallel, with $90$ edges in all.
Its impedance function for an orientation vector with $a_j$ tall edges in the $j$-th block is $sum_j x slash (a_j + (9 - a_j) x^2)$, every point is regular, and the number of pairs of an orientation vector and a solution $x > 1$ of $F(x) = 1$, counted in exact arithmetic by the changes of sign of $N - D$ at rational points, is at least $1.008 dot.op 2^(90)$.
Distinct orientation vectors give pairs that are not isomorphic, since an isomorphism of this plane network with itself fixes the poles and $e_0$, and then every edge in turn; so this network has more tilings of the square of proportion larger than $1$ than orientation vectors.
For $n <= 9$, on the other hand, no network has more such tilings than it has orientation vectors with a regular full-side root.

== The rate of growth <sec:growth-rate>

By @prop:upper the numbers $a(n)$ grow at most like $(27 slash 2)^n$, and the values computed are compatible with that rate.
It is nevertheless not attained, by $a(n)$ or by $t(n)$: a pair that contains a certain local pattern has no regular point, hence gives no tiling by @prop:full-side, and the pairs that avoid a local pattern grow more slowly than all pairs.

#definition(name: [square block])[
  A _square block_ of a pair $(frak(N), epsilon)$ is a face of $G^+$ whose boundary is a cycle of four edges $a$, $b$, $d$, $c$ of $G$, where $a$ joins a vertex $u$ to a vertex $v_1$, $b$ joins $v_1$ to a vertex $w$, $c$ joins $u$ to a vertex $v_2$ and $d$ joins $v_2$ to $w$, such that $v_1$ and $v_2$ have degree two in $G^+$ and the four edges have the same orientation.
] <def:square-block>

In a tiling, two tiles of the same orientation stacked between the same two segments are congruent, and two such stacks side by side form four congruent tiles that meet at a point; the two vertices of degree two would then coincide.

#proposition[
  A pair with a square block has no regular point.
] <prop:square-block>

#proof[
  The vertex $v_1$ lies on $a$ and $b$ only, so it is not a pole, since the poles are ends of $e_0$; likewise $v_2$.
  Let $x > 0$ be such that no current of the flow of value $1$ vanishes, and let $r := x^(epsilon_a)$ be the common resistance of the four edges.
  By Kirchhoff's law at $v_1$ the same current $j_1$ flows through $a$ and $b$ from $u$ to $w$, and likewise a current $j_2$ through $c$ and $d$.
  By Ohm's law, $phi(u) - phi(w) = 2 r j_1 = 2 r j_2$, so that $j_1 = j_2 =: j$ and $phi(v_1) = phi(u) - r j = phi(v_2)$.
  We may name the vertices so that $j > 0$; then $a$ and $c$ are directed from $u$, with heads $v_1$ and $v_2$.
  The face lies on one side of its boundary, along which $a$ and $c$ are traversed in opposite senses, so that it is $lft(a) = rgt(c)$ or $rgt(a) = lft(c)$.
  In either case its value under $psi$ is the abscissa of the right side of one of $rct(a)$, $rct(c)$ and of the left side of the other, and the bottom sides of the two rectangles are at the same height; so they have a common end, which lies in $S_(v_1)$ and in $S_(v_2)$, and the flow is not regular.
]

#proposition[
  Let $(frak(N), epsilon)$ be a pair with $n$ edges, with $G^+$ non-separable and without a square block, and let $S$ be a set of $k$ of its edges.
  Replace every edge $e in S$, with ends $u$ and $w$, by six edges of the orientation of $e$: two edges joining $u$ and $w$ and, between them in the drawing, two paths of two edges from $u$ to $w$ through new vertices $v_1$ and $v_2$.
  + The result is a pair with $n + 5 k$ edges, with $G^+$ non-separable.
  + Its square blocks are the $k$ faces bounded by the two paths of a replaced edge.
  + The isomorphism class of the result determines that of $(frak(N), epsilon)$ and, under the isomorphism, the set $S$.
] <prop:substitution>

#proof[
  For the first statement, the edge $e_0$ and the poles are unchanged, and there are no loops.
  If a new vertex is removed, what remains contains a copy of $G^+$ in which each replaced edge is represented by one of the two edges that join its ends, and the other new vertices are attached to it.
  If an old vertex $y$ is removed, $G^+ - y$ is connected, each replaced edge not at $y$ is again represented, and every new vertex remains joined to an end of its edge other than $y$.

  For the second, the new faces at a replaced edge are two triangles, each bounded by one of the two edges that join $u$ and $w$ and by one of the paths, and the quadrilateral bounded by the two paths; every other face is a face of the original with some edges replaced by one of the edges that join their ends, and has the same number of sides.
  The degree of an old vertex increases by three for every replaced edge at it, and the ends of a replaced edge have degree at least four.
  Let a face be a square block of the result, with vertices $v'_1$ and $v'_2$ of degree two.
  If $v'_1$ is new, the two faces at it are a triangle and the quadrilateral of its edge, so the face is that quadrilateral.
  If both are old, no edge at them has been replaced; the four edges of the face are the edges at $v'_1$ and $v'_2$, so they are old, and the face is a face of the original with the same boundary, degrees and orientations, hence a square block of the original, contrary to the hypothesis.
  Conversely each of the $k$ quadrilaterals is a square block.

  For the third, an isomorphism between two results maps square blocks to square blocks.
  For each square block, the two edges that join its vertices $u$ and $w$ are determined as a pair: they are the third sides of the two triangles across its paths.
  Deleting the two vertices of degree two and one of these two edges at every square block gives a pair that does not depend on the choice, up to the name of the edge kept, and that is the original pair with the kept edges forming $S$.
  So the isomorphism induces one of the original pairs that maps $S$ to $S$; and a plane network has no isomorphism with itself other than the identity, since such an isomorphism fixes $e_0$ and its ends and then, by the cyclic orders, every edge in turn.
]

#proposition[
  Let $A(n)$ be the number of isomorphism classes of pairs with $n$ edges with $G^+$ non-separable and without a square block, and let
  $ lambda := (27 slash 2) / (1 + (2 slash 27)^5) = 13.49996... $
  There is a constant $C$ such that, for every $n >= 1$,
  $ g(n) <= A(n) <= C lambda^n, quad t(n) <= (n + 1) A(n). $
  Consequently
  $ limsup_(n -> infinity) a(n)^(1 slash n) <= limsup_(n -> infinity) t(n)^(1 slash n) <= lambda < 27 / 2. $
] <prop:deficit>

#proof[
  The isomorphism classes of pairs with $m$ edges and $G^+$ non-separable are at most $2^m M(m)$, as in the proof of @prop:upper: the plane network is a non-separable planar map rooted at $e_0$, and it has $2^m$ orientation vectors.
  By @prop:substitution, a class counted by $A(n)$ and a set of $k$ of its edges give a class with $n + 5 k$ edges and exactly $k$ square blocks, and different data give different classes; hence
  $ sum_(n + 5 k = m) binom(n, k) A(n) <= 2^m M(m) quad "for every" m. $
  Let $rho := 2 slash 27$.
  Multiplying by $rho^m$ and summing over $m$, which is permitted since all terms are non-negative,
  $ sum_n A(n) (rho + rho^6)^n = sum_m rho^m sum_(n + 5 k = m) binom(n, k) A(n) <= sum_m M(m) (4 slash 27)^m =: C, $
  which is finite because $M(m)$ is asymptotic to a constant times $(27 slash 4)^m m^(-5 slash 2)$.
  Each term of the sum on the left is at most $C$, and $1 slash (rho + rho^6) = lambda$; so $A(n) <= C lambda^n$.

  A pair with a regular point is isomorphic to the pair of a tiling, by the first statement of @prop:reconstruction, so that its graph $G^+$ is non-separable by @prop:nonseparable, and it has no square block by @prop:square-block.
  Hence $g(n) <= A(n)$.
  By the first statement of @prop:full-side, $t(n) - s(n)$ is the number of triples of such a pair and a regular point $x > 1$ at which its impedance function is $1$; a pair has at most $n$ such points, by the fifth statement of @prop:reactance, so that $t(n) - s(n) <= n A(n)$.
  A tiling $sigma$ of the unit square by squares gives the pair of $frak(N)(sigma)$ with all edges wide, whose impedance function is $1 slash x$ and whose flows are those of unit resistances with the potential divided by $x$, so that every point is regular by the second statement of @prop:reconstruction; distinct tilings give pairs that are not isomorphic, so that $s(n) <= A(n)$.
  Finally $a(n) <= t(n)$, since every proportion is that of a tiling.
]

The constant $C$ is numerically $0.25$.
The bound gives nothing for the values of $n$ computed: the factor $(1 + (2 slash 27)^5)^(-n)$ is $0.99997$ for $n = 13$, and $C (n + 1) lambda^n$ falls below the bound of @prop:upper only for $n$ of the order of $10^7$.
Its interest is that the rate $27 slash 2$ of the planar maps is not that of the tilings.
The pattern can be widened, to four edges with $epsilon_a + epsilon_d = epsilon_b + epsilon_c$, which lowers the bound slightly; and other patterns have the same effect.
For nine tiles $0.6$ per cent of the pairs have a square block, while $3.3$ per cent have no regular full-side root.

Whether the sequences have a rate of growth at all is not known.

#conjecture[
  The sequence $t(n)^(1 slash n)$ converges.
] <conj:rate-tilings>

#conjecture[
  The sequence $a(n)^(1 slash n)$ converges.
] <conj:rate>

By @prop:deficit the limits, if they exist, are smaller than $27 slash 2$.
The values computed do not show this.
If $a(n)$ were a constant times $mu^n n^(-gamma)$, then $gamma$ would be $log(mu a(n) slash a(n + 1)) slash log((n + 1) slash n)$ for every $n$.
For $mu = 27 slash 2$ this quantity takes the values $5.81$, $5.76$, $5.66$, $5.56$, $5.515$ and $5.514$ for $n = 7, dots, 12$, and the quotient of $a(n)$ by $(27 slash 2)^n n^(-11 slash 2)$ takes the values $0.6825$, $0.6783$, $0.6774$ and $0.6767$ for $n = 10, dots, 13$; similarly, the quotient of $t(n)$ by $2^n M(n)$ increases slowly, to $0.2920$ for twelve tiles.
These fits, which @fig:sequences shows, describe only the terms computed: by @prop:deficit both quotients tend to zero.
A deficit of the size proved, or of the size that the proportion of pairs without regular points suggests, cannot be detected in thirteen terms.

== Mosaic classes <sec:mosaic>

The equations that a tiling imposes on the sizes of its tiles depend only on which tiles border each maximal segment, and not on the order in which the corners of tiles on the two sides of a segment alternate.
This section records that point of view, which motivates the placement rules; nothing in it is used in the proofs of correctness, and none of it is part of the formal development.

#definition(name: [mosaic class])[
  A _segment_ of a tiling is a maximal line segment contained in the union of the boundaries of the tiles and not contained in the boundary of the main rectangle, or one of the four sides of the main rectangle.
  Two tilings with $n$ tiles are _mosaic equivalent_ if their tiles can be numbered so that, for each side of each tile, the tiles whose opposite side lies on the same segment are the same in both, and the segments containing the four sides of the main rectangle correspond.
] <def:mosaic>

@fig:mosaic shows two tilings of the same mosaic class.

#figure(
  image("figures/mosaic.svg", width: 48%),
  caption: [Two tilings of the square by five tiles, of proportions $6 slash 5$ and $1.6823...$, whose records have the same placements and differ in the orientation of the last tile. The same tiles lie on either side of each segment, but along the vertical segment the junction on the right lies between the two on the left in the first tiling, and below both in the second.],
) <fig:mosaic>

Mosaic classes of tilings in which no four tiles meet at a point are the mosaic floorplans of the literature on rectangulations, which are counted by the Baxter numbers $B(n)$ @yao2003 @ackerman2006 @chung1978; the finer classification that also records the alternation of corners along segments gives the generic rectangulations @reading2012.
The staircase construction never distinguishes the order of corners along a vertical segment, and the rule on started floors fixes it along horizontal ones.
For every $n <= 13$ the number of complete admissible records for $n$ tiles, disregarding orientations, is $B(n)$ @oeisA001181.
This agreement is an observation, made by computation.
That a tiling without a point where four tiles meet arises from only one record, for given orientations, is proved in @prop:representative, though not formally; the correctness of the search does not depend on it.

In terms of electrical networks @bsst1940, each horizontal segment is a node, each tile is a resistor joining the segment that contains its top side to the one that contains its bottom side, the width of a tile is the current through it and its height the potential difference across it.
A wide tile has resistance $1 slash x$ and a tall one resistance $x$.
The equations of a record express Kirchhoff's laws for this network, which is determined by the mosaic class, and for positive resistances these laws determine the currents @kirchhoff1847 @bsst1940.
One therefore expects the equations of every record to have exactly one solution for each $x > 0$, up to scale.
We have not proved this expectation, and the search does not rely on it: it counts the records for which it fails, in the form made precise in @def:regular, and its results are certified only if there are none.

The same bound for the number of realisations of @tab:counts, that is, of the pairs of a record in which the first tile is wide and a proportion that it realises, is proved only conditionally.
The proof of @prop:upper bounds the number of triples of a rooted map, an orientation vector and a proportion.
The network of the tiling cannot be used here, since by @prop:multiplicity a tiling with crossings has several records and one network.
Associate instead with a record the network whose vertices are the horizontal segments created by its placements, where two segments of equal height that meet at a crossing are kept distinct and joined in the order given by the record; the tiling still gives a flow on it, in which no current vanishes.
The map that sends a record with orientations and a proportion to the triple of this network with the edge joining its poles, the orientations and the proportion is injective provided that, first, different records, disregarding orientations, belong to different mosaic classes, secondly, a mosaic class is determined by its plane network together with the directions of its edges, and, thirdly, the network of a record with the added edge is a non-separable planar map.
Given the second condition, the class is recovered from the map, the orientations and the proportion, because the directions are those of the currents, which are determined by @prop:flow.
The first condition is the agreement with the Baxter numbers observed above, which we have not proved, and the third would follow from it if every sequence were that of a tiling by rectangles without crossings.
The second is the correspondence between mosaic classes and plane bipolar orientations, both of which are counted by the Baxter numbers @bonichon2010 @felsner2011; it is not proved here, and we have not verified that these references give it in the form needed.
So the number of realisations with $n$ tiles is at most $n 2^(n - 1) M(n)$ if the three conditions hold, and we do not claim the bound otherwise.
The correspondence would also explain why $M(5) = 91$ is smaller than the number $92$ of mosaic classes with five tiles: the two pinwheels of five tiles have the same network and differ in the direction of the central edge.

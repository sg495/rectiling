# Proofs of the structural claims

This note takes the statements of [analysis.md](analysis.md) that were labelled *Argued* or *Conjecture* and records what can be proved about them.
Each section gives a precise statement, its status and a proof; where a proof depends on a result from the literature or on a computation, the dependence is named.
The first claim is also proved formally, in the Lean development of [`lean/`](../lean/README.md).

The proofs in this note, other than the formalised ones, were read line by line by an independent reviewer, who re-derived the computations, repeated the case analyses of Section 4 with a separate exhaustive enumeration of dissections into squares, and tested Theorem 2.6 exactly on four hundred random networks; the repairs requested have been made.
The reviewer did not examine Remark 6.3 or the open conjectures, and did not read Tutte's paper in the original.

## Summary

- **Persistence, $S(n) \subseteq S(n+k)$.** Proved in full and formalised in Lean (Theorem 1.1).
- **Shape of the aspect-ratio function.** Proved in full from the linear system (Theorem 2.6).
- **$N - D$ determines $\{R, 1/R\}$.** Proved in full (Corollary 2.7).
- **Parity law.** Proved in full (Corollary 2.8).
- **Wide rectangles count the functions.** Proved, after a correction to the definition of $E(n)$, using standard facts of planar duality (Theorem 3.6).
- **The three rational proportions lie in $S(n)$.** Proved in full (Proposition 4.1).
- **They need both orientations.** Proved in full, by hand (Theorem 4.6).
- **There are no other such proportions for $n \ge 10$.** Open (Conjecture 4.8).
- **Explicit width.** $W(n) = n(1 + 4^n/2)$ is proved, assuming Kirchhoff's tree formulas (Proposition 5.1).
- **Threshold $\lfloor n^2/4 \rfloor + 2$.** Open; only a lower bound on the threshold is proved (Proposition 5.2).
- **$a(n) \le n\,2^{n-1} M(n)$.** Proved, assuming Tutte's enumeration of non-separable planar maps (Theorem 6.2).
- **$T(n) \le n\,2^{n-1} M(n)$.** Proved in part: two combinatorial facts are assumed (Remark 6.3).
- **$g(n) \le n \cdot A338781(n)$.** Proved in full (Proposition 6.4); the growth constant $6.159$ is numerical.
- **Log-convexity of $a(n)$, the bound of the wide counts by $E(n)$, and $g(n)/a(n) \to 0$.** Open (Section 7).

Several statements of the analysis needed correcting; see Section 8.

## 0. Conventions

A *tiling* of a rectangle $[0,W] \times [0,H]$ is a finite family of closed axis-parallel rectangles with positive sides, the *tiles*, whose interiors are pairwise disjoint and whose union is the rectangle.
A tile has *proportion* $x \ge 1$ if one of its sides is $x$ times the other; it is *wide* if its width is $x$ times its height and *tall* if its height is $x$ times its width.
For $x = 1$ a tile is both, and an orientation is then any choice of label.
$S(n)$ is the set of $x \ge 1$ for which the unit square has a tiling by $n$ tiles of proportion $x$, and $a(n) = |S(n)|$.
The *transpose* of a tiling is its image under the reflection that exchanges the two coordinates; it exchanges wide and tall tiles.

## 1. Persistence

**Theorem 1.1.** Let $n \ge 2$ and $k \ge 3$. Then $S(n) \subseteq S(n+k)$.
For proportions $x > 1$ the same holds for every $n \ge 1$.

*Status.* Proved in full, and formalised in Lean with no `sorry` (`Rectiling.persistence`, `Rectiling.persistence_of_one_lt`).

*Proof.*
Every $k \ge 3$ is $3$, $4$ or $5$ plus a multiple of $3$, so it suffices to gain three, four and five tiles.

*Three.* The two mid-lines of a tile cut it into four rectangles with half its sides, which have its proportion.
Replacing one tile by these four gives a tiling by $n + 3$ tiles.

*Five.* Let a tile have width $u$ and height $v$.
The rectangle of sides $2u/3$ and $2v/3$ in its bottom-left corner, together with five rectangles of sides $u/3$ and $v/3$, two above it and three in a column on the right, tile it.
All six have the proportion of the tile, and replacing the tile by them gives $n + 5$ tiles.

*Four, for $x > 1$.* Put $q = 1/(x+1)$ and $p = x/(x+1)$, so that $p + q = 1$, $p = xq$ and $q < p$.
The rectangles $[0,p] \times [0,q]$, $[p,1] \times [0,p]$, $[q,1] \times [p,1]$ and $[0,q] \times [q,1]$ have proportion $x$, and together with the square $[q,p]^2$ they tile the unit square.
The image of the given tiling under the homothety of ratio $p - q$ followed by the translation by $(q,q)$ tiles $[q,p]^2$ by $n$ tiles of proportion $x$.
Together these are $n + 4$ tiles.

*Four, for $x = 1$.* It suffices that $1 \in S(m)$ for every $m \ge 6$, since $n + 4 \ge 6$.
The cut of the square into six squares described above gives $m = 6$.
Cutting the square in four, and one of the four in four again, gives $m = 7$.
A square of side $3/4$ with seven squares of side $1/4$ along two of its sides gives $m = 8$.
Every other $m \ge 9$ is reached from these by steps of three. $\square$

The hypothesis $n \ge 2$ is needed only for $x = 1$ and $k = 4$: $1 \in S(1)$ and $1 \notin S(5)$, by Lemma 4.2 below.
The Lean statement is in terms of the predicate `Achievable n x`, which says that the unit square has a tiling, in the sense of `IsSimilarTiling`, by a list of $n$ rectangles of proportion $x$.
The Lean proof follows the argument above; its single geometric tool is `IsTiling.refine`, the replacement of a tile by a tiling of that tile.
The steps of three and five are proved for an arbitrary main rectangle (`TilesWith.add_three`, `TilesWith.add_five`).
The step of four is proved for the square only: in a main rectangle with $W \ne H$, the pinwheel of two wide and two tall tiles used above leaves a central rectangle that is not similar to the main one.

**Proposition 1.2.** $1 \in S(n)$ exactly for $n = 1$, $n = 4$ and $n \ge 6$.

*Status.* Proved in full; the case $n \ge 6$ of the positive part is in Lean (`achievable_one`), within whose proof the case $n = 4$ appears.

*Proof.*
If $n \ge 2$, no tile contains two corners of the square, since a square containing two corners of the unit square is the unit square.
So there are at least four tiles, and $n = 5$ is excluded by Lemma 4.2.
The cases $n = 4$ and $n \ge 6$ were constructed above. $\square$

That steps of one and of two fail in general is a matter of data: $2 \in S(2)$ lies neither in $S(3)$ nor in $S(4)$.

## 2. The aspect-ratio function

### 2.1 Networks

A *network* $\mathfrak N = (G, s, t)$ is a finite connected graph $G = (V, E)$, possibly with multiple edges but without loops, with two distinct vertices $s$ and $t$, the *poles*.
Fix a reference direction for every edge $e$, from its tail $e^-$ to its head $e^+$.
Let $r \colon E \to \mathbb C \setminus \{0\}$ be a function, the *resistances*, and $y_e = 1/r_e$ the *conductances*.
A *flow of value $I$* is a pair of functions $\varphi \colon V \to \mathbb C$ and $i \colon E \to \mathbb C$ such that

- (Ohm) $\varphi(e^-) - \varphi(e^+) = r_e\, i_e$ for every edge $e$;
- (Kirchhoff) $\sum_{e^- = v} i_e - \sum_{e^+ = v} i_e = I\,(\delta_{vs} - \delta_{vt})$ for every vertex $v$.

Let $B$ be the incidence matrix, with $B_{ve} = 1$ if $v = e^-$, $-1$ if $v = e^+$ and $0$ otherwise, let $Y$ be the diagonal matrix of the conductances, and $L = B Y B^{\mathsf T}$.
A pair $(\varphi, i)$ is a flow of value $I$ exactly when $i = Y B^{\mathsf T} \varphi$ and $L \varphi = I(\delta_s - \delta_t)$.
Write $L_t$ for $L$ with the row and column of $t$ removed, and $L_{st}$ for $L$ with the rows and columns of $s$ and $t$ removed; the determinant of an empty matrix is $1$.

**Lemma 2.1.** Suppose that $\operatorname{Re} r_e > 0$ for every edge, or that $\operatorname{Re} r_e < 0$ for every edge.

1. For every $I$ there is a flow of value $I$, and $\varphi$ is unique up to an additive constant.
2. $\det L_t \ne 0$, and the *impedance* $Z = (\varphi(s) - \varphi(t))/I$, for $I \ne 0$, equals $\det L_{st} / \det L_t$.
3. $\operatorname{Re} Z$ has the sign of the $\operatorname{Re} r_e$.

*Proof.*
The numbers $\operatorname{Re} y_e = \operatorname{Re} r_e / |r_e|^2$ have the sign of the $\operatorname{Re} r_e$; suppose they are positive, the other case being the same.
For $\varphi \in \mathbb C^V$, $\bar\varphi^{\mathsf T} L \varphi = \sum_e y_e\, |\varphi(e^-) - \varphi(e^+)|^2$.
If $L \varphi = 0$, the real part of this identity shows that $\varphi$ takes equal values at the two ends of every edge, hence is constant, as $G$ is connected.
So the kernel of $L$ is the line of constants and $L$ has rank $|V| - 1$.
The image of $L$ lies in the hyperplane of vectors with zero sum, because $\mathbf 1^{\mathsf T} L = 0$, and so equals it.
This gives (1).
If $L_t \varphi' = 0$, extend $\varphi'$ to $\varphi$ by $\varphi(t) = 0$; then $(L\varphi)_v = 0$ for $v \ne t$, so $\bar\varphi^{\mathsf T} L \varphi = \overline{\varphi(t)}\,(L\varphi)_t = 0$, whence $\varphi$ is constant and $\varphi' = 0$.
So $L_t$ is invertible; the flow of value $1$ with $\varphi(t) = 0$ has $\varphi(s) = (L_t^{-1})_{ss} = \det L_{st}/\det L_t$ by Cramer's rule, which is (2).
For the flow of value $1$, $\bar\varphi^{\mathsf T} L \varphi = \bar\varphi^{\mathsf T}(\delta_s - \delta_t) = \bar Z$, so $\operatorname{Re} Z = \sum_e \operatorname{Re}(y_e)\,|\varphi(e^-) - \varphi(e^+)|^2$.
This is positive, since $\varphi$ is not constant. $\square$

**Lemma 2.2 (maximum principle).** Let the resistances be real and positive and $I > 0$. Then $\varphi(t) \le \varphi(v) \le \varphi(s)$ for every vertex $v$, and $1/Z \le \sum_{e \ni s} y_e$.

*Proof.*
Let $M$ be the set of vertices at which $\varphi$ is largest, and suppose $s \notin M$.
At $v \in M$ the law of Kirchhoff reads $\sum_{e \ni v} y_e(\varphi(v) - \varphi(v_e)) = -I\,\delta_{vt} \le 0$, where $v_e$ is the other end of $e$; every term is non-negative, so every neighbour of $v$ lies in $M$.
By connectedness $M = V$, which contradicts the fact that $\varphi$ is not constant, as $I > 0$; so $s \in M$, and likewise $\varphi$ is smallest at $t$.
The law of Kirchhoff at $s$ then gives $I = \sum_{e \ni s} y_e(\varphi(s) - \varphi(v_e)) \le (\varphi(s) - \varphi(t)) \sum_{e \ni s} y_e$. $\square$

**Lemma 2.3.** The determinants $\det L_t$ and $\det L_{st}$ are polynomials in the $y_e$ with integer coefficients, homogeneous of degrees $|V| - 1$ and $|V| - 2$, and of degree at most one in each variable.

*Proof.*
$L = \sum_e y_e\, b_e b_e^{\mathsf T}$, where $b_e$ is the column of $B$; the same holds for the two submatrices, with the $b_e$ truncated.
Homogeneity is clear, and $\det(A + y\,u u^{\mathsf T}) = \det A + y\,u^{\mathsf T} \operatorname{adj}(A)\,u$ has degree at most one in $y$. $\square$

### 2.2 The network of a tiling

Let $\tau$ be a tiling of $[0,W] \times [0,H]$ by $n$ tiles of any shapes.
Let $U$ be the union of the top and bottom sides of all tiles, and let the vertices be the connected components of $U$; each is a horizontal segment of positive length.
The top side of the main rectangle is one component, $s$, and the bottom side another, $t$.
Each tile is an edge, directed from the component that contains its top side to the component that contains its bottom side.
This is the network $\mathfrak N(\tau)$ of Brooks, Smith, Stone and Tutte (1940); with the definition by components, it is defined also when four tiles meet at a point.
Give the tile $T$ of width $a_T$ and height $b_T$ the resistance $r_T = b_T / a_T$.

**Proposition 2.4.** $\mathfrak N(\tau)$ is a network.
With $\varphi(C)$ the height of the component $C$ and $i_T = a_T$, the pair $(\varphi, i)$ is a flow of value $W$ with $\varphi(s) - \varphi(t) = H$.
Hence $H/W$ is the impedance of $\mathfrak N(\tau)$ for the resistances $r_T$.
Moreover $\mathfrak N(\tau)$ has an embedding in the plane with both poles on the outer face.

*Proof.*
The law of Ohm holds by the choice of the resistances.
Let $C = [a,b] \times \{c\}$ be a component with $c < H$, and let $(u, c)$ be a point of $C$ whose abscissa is not that of a corner of a tile.
For small $\eta > 0$ the point $(u, c + \eta)$ is interior to a tile $T$, the same for all small $\eta$.
If $c$ were interior to the vertical extent of $T$, the point $(u,c)$ would be interior to $T$; but it lies on a side of some tile $T'$, so the interiors of $T$ and $T'$ would meet, and $T' = T$ is impossible.
So the bottom side of $T$ is at height $c$; it meets $C$ and is connected, so it lies in $C$.
The tiles whose bottom side lies in $C$ thus cover $C$ up to finitely many points, and their bottom sides do not overlap, so their widths add up to $b - a$.
In the same way, if $c > 0$, the widths of the tiles whose top side lies in $C$ add up to $b - a$.
This is the law of Kirchhoff at an inner component, and for $s$ and $t$ it gives the value $W$.
Every component at positive height carries the top side of some tile, whose bottom side lies on a lower component; descending, one reaches $t$, so the graph is connected.
A tile joins components at different heights, so there are no loops.
For the embedding, represent each tile by the vertical segment through its centre, between its top and bottom sides, and contract each component to a point.
The poles are joined by a curve outside the main rectangle, so they lie on a common face, which may be taken as the outer one. $\square$

### 2.3 The function

Let $\mathfrak N$ be a network with $n$ edges and $\varepsilon \in \{+1, -1\}^E$ an *orientation vector*.
Give the edge $e$ the resistance $x^{\varepsilon_e}$: $x$ for a tall tile, $1/x$ for a wide one.

**Definition 2.5.** $Z_{\mathfrak N, \varepsilon} \in \mathbb Q(x)$ is the rational function $\det L_{st}/\det L_t$ evaluated at $y_e = x^{-\varepsilon_e}$.

The denominator is a Laurent polynomial that does not vanish at $x = 1$, so the definition makes sense, and by Lemma 2.1 the value of $Z_{\mathfrak N,\varepsilon}$ at any $x > 0$ is the impedance of the network.
By Proposition 2.4, a tiling $\tau$ of $[0,W] \times [0,H]$ by tiles of proportion $x$, with orientations $\varepsilon$, satisfies $H/W = Z_{\mathfrak N(\tau), \varepsilon}(x)$.
The function $R$ of the analysis, the aspect ratio of the main rectangle for a fixed arrangement and fixed orientations, is this function or its inverse, according to the convention; the inverse is a function of the same kind, being that of the transposed tiling (see also Lemma 3.3, which applies because the network of a tiling with the edge joining its poles has no bridge, by Lemma 6.1).

A rational function $F \in \mathbb Q(x)$ is written *in lowest terms* as $F = N/D$ with $N, D \in \mathbb Z[x]$ coprime in $\mathbb Q[x]$, with no common integer factor other than $\pm 1$, and with the leading coefficient of $D$ positive.
This determines $N$ and $D$.

**Theorem 2.6.** Let $F = Z_{\mathfrak N, \varepsilon}$ for a network with $n$ edges, and $F = N/D$ in lowest terms.

1. $F(-x) = -F(x)$.
2. For complex $x$ with $\operatorname{Re} x > 0$, $D(x) \ne 0$ and $\operatorname{Re} F(x) > 0$. In particular $F$ is finite and positive on $(0, \infty)$.
3. All complex roots of $N$ and of $D$ are simple and lie on the imaginary axis.
4. The coefficients of $N$ and $D$ are non-negative integers. One of $N$, $D$ is an even polynomial with non-zero constant term, and the other is an odd polynomial in which $x$ has multiplicity one.
5. $\deg N - \deg D = \pm 1$, and $\deg N, \deg D \le n$. If at most $k$ edges have orientation $+1$, or at most $k$ have orientation $-1$, then $\deg N, \deg D \le 2k + 1$.
6. There are $c_\infty, c_0 \ge 0$, and $\kappa_j > 0$, $\omega_j > 0$ with the $\omega_j$ distinct, such that
   $$F(x) = c_\infty x + \frac{c_0}{x} + \sum_j \frac{2 \kappa_j x}{x^2 + \omega_j^2}.$$
   Consequently $F(x)/x$ is non-increasing and $x F(x)$ is non-decreasing on $(0,\infty)$.

*Status.* Proved here in full, from the linear system.
Statements (2), (3) and (6) are the classical properties of the impedance of a network of inductors and capacitors (Foster's reactance theorem); the proof is included because it is short.

*Proof.*
(1) Replacing $x$ by $-x$ replaces every $y_e = x^{\mp 1}$ by $-y_e$.
By Lemma 2.3 this multiplies $\det L_{st}$ by $(-1)^{|V|-2}$ and $\det L_t$ by $(-1)^{|V|-1}$.

(2) If $\operatorname{Re} x > 0$ then $\operatorname{Re} x^{\pm 1} > 0$.
By Lemma 2.1 the Laurent polynomial $q(x) = \det L_t$ does not vanish at $x$, and $p(x)/q(x)$, with $p = \det L_{st}$, has positive real part there.
As rational functions $N q = D p$.
If $D(x) = 0$ then $N(x)\,q(x) = 0$, so $N(x) = 0$, which contradicts coprimality.
So $D(x) \ne 0$ and $F(x) = p(x)/q(x)$.

(3) By (1), $N(-x)\,D(x) = -N(x)\,D(-x)$.
As $N$ and $D$ are coprime, $N(x)$ divides $N(-x)$, which has the same degree, so $N(-x) = \pm N(x)$, and then $D(-x) = \mp D(x)$.
So each of $N$ and $D$ is an even or an odd polynomial, and its roots are symmetric about the origin.
By (2) neither has a root with positive real part: for $D$ this was shown, and $N(x) = 0$ would give $F(x) = 0$.
By symmetry neither has a root with negative real part.
Let $\mathrm i\omega$, with $\omega$ real, be a root of $N$ of multiplicity $m$.
Then $F(\mathrm i\omega + \rho\,\mathrm e^{\mathrm i\theta}) = A \rho^m \mathrm e^{\mathrm i m \theta}(1 + O(\rho))$ with $A \ne 0$, and by (2) the real part is positive for $|\theta| < \pi/2$.
Letting $\rho \to 0$ gives $\operatorname{Re}(A\,\mathrm e^{\mathrm i m\theta}) \ge 0$ for all $|\theta| < \pi/2$.
For $m \ge 2$ the argument $m\theta$ covers an interval of length at least $2\pi$, on which this fails.
So $m = 1$; the same argument applied to $1/F$, which also has positive real part on the right half-plane, treats the roots of $D$.

(4) A real polynomial with positive leading coefficient whose roots are simple and purely imaginary is a positive multiple of $x^a \prod_j (x^2 + \omega_j^2)$ with $a \in \{0, 1\}$, and has non-negative coefficients.
The leading coefficient of $N$ is positive because $F > 0$ on $(0,\infty)$.
By (1), $N$ and $D$ have opposite parities, so exactly one of them is odd; it is divisible by $x$, exactly once by (3), and the other is not divisible by $x$, by coprimality.

(5) Let $\delta = \deg N - \deg D$, an odd number by (4).
For large $|x|$, $F(\rho\,\mathrm e^{\mathrm i\theta}) = A \rho^\delta \mathrm e^{\mathrm i \delta\theta}(1 + O(1/\rho))$, and the argument of (3) gives $|\delta| \le 1$.
Let $P(r) = \prod_e r_e \cdot \det L_{st}(1/r)$ and $Q(r) = \prod_e r_e \cdot \det L_t(1/r)$.
By Lemma 2.3 these are polynomials in the resistances, of degree at most one in each, and homogeneous of degrees $c + 1$ and $c$, where $c = n - |V| + 1$.
A monomial of $Q$ is a product of $c$ distinct resistances, $j$ of them equal to $x$ and $c - j$ equal to $1/x$, so it is $x^{2j - c}$; if $m$ edges have orientation $-1$ then $c - j \le m$ and $j \le n - m$, so $x^m$ times the monomial is a power of $x$ with exponent between $0$ and $n$.
The same holds for $P$.
So $F = x^m P / x^m Q$ is a quotient of two polynomials of degree at most $n$, and $N$ and $D$ divide them.
If at most $k$ edges have orientation $+1$, then $j \le k$ in every monomial, so the exponents of $Q$ lie in $[-c, 2k - c]$ and those of $P$ in $[-c-1, 2k - c - 1]$; after multiplication by $x^{c+1}$ both are polynomials of degree at most $2k+1$.
If at most $k$ edges have orientation $-1$, apply this to $x \mapsto 1/x$.

(6) By (3) and (5), $F$ has simple poles at some points $\pm\mathrm i\omega_j$, possibly a simple pole at $0$, and at infinity $F(x) - c_\infty x$ is bounded, where $c_\infty \ge 0$ is the quotient of the leading coefficients if $\deg N > \deg D$ and zero otherwise.
Near a pole $\mathrm i\omega$, $F(\mathrm i\omega + \rho\,\mathrm e^{\mathrm i\theta}) = \kappa \rho^{-1} \mathrm e^{-\mathrm i\theta}(1 + O(\rho))$, and positivity of the real part for $|\theta| < \pi/2$ forces $\kappa > 0$.
By (1) the residue at $-\mathrm i\omega$ is the same, and $\kappa/(x - \mathrm i\omega) + \kappa/(x + \mathrm i\omega) = 2\kappa x/(x^2 + \omega^2)$.
The difference between $F$ and the right-hand side of the formula is a rational function without poles that is bounded at infinity, hence a constant, and it is odd, hence zero.
Finally $F(x)/x = c_\infty + c_0/x^2 + \sum_j 2\kappa_j/(x^2 + \omega_j^2)$ and $x F(x) = c_\infty x^2 + c_0 + \sum_j 2\kappa_j x^2/(x^2 + \omega_j^2)$. $\square$

By (5), $F(x)$ tends to $0$ or to $\infty$ as $x \to \infty$, and by (4) likewise as $x \to 0^+$.
Reversing all orientations replaces $F(x)$ by $F(1/x)$, since it inverts every resistance as a function of $x$.

The properties were also tested numerically on 300 random networks with up to nine edges.

**Corollary 2.7.** For $F$ as in Theorem 2.6, the polynomial $N - D$ is primitive, and it determines the unordered pair $\{F, 1/F\}$; so does $D - N$, and so does the pair $\{N - D, D - N\}$.

*Proof.*
$N$ and $D$ have no monomial in common, by (4), so the coefficients of $N - D$ are those of $N$ and $-D$, whose greatest common divisor is $1$.
Let $P = \pm(N - D)$, and let $P_0$ and $P_1$ be its even and odd parts.
Then $\{N, D\} = \{\pm P_0, \pm P_1\}$, and the signs are those that make the leading coefficients positive.
So $P$ determines $\{N, D\}$, and with it $\{N/D, D/N\}$. $\square$

**Corollary 2.8 (parity law).** For $F$ as in Theorem 2.6, let $d = \deg(N - D)$, and let $\varrho$ be the number of roots of $N - D$ in $(0,\infty)$, counted with multiplicity; these are the solutions of $F(x) = 1$.
If $F$ tends to $0$ at one end of $(0,\infty)$ and to $\infty$ at the other, then $d$ and $\varrho$ are odd; otherwise both are even.

*Proof.*
$d = \max(\deg N, \deg D)$, and the leading coefficient of $N - D$ is positive if $\deg N > \deg D$, that is if $F \to \infty$ at infinity, and negative otherwise.
Exactly one of $N(0)$, $D(0)$ is zero, so $N(0) - D(0)$ is negative if $N$ is the odd polynomial, that is if $F \to 0$ at $0^+$, and positive otherwise.
The parity of $\varrho$ is odd exactly when the value at $0$ and the leading coefficient have opposite signs.
If $F \to 0$ at $0^+$ and $F \to \infty$ at infinity, the signs are opposite and $d = \deg N$ is odd, as $N$ is odd.
If $F \to \infty$ at $0^+$ and $F \to 0$ at infinity, the signs are opposite and $d = \deg D$ is odd, as $D$ is odd.
If $F \to 0$ at both ends, the signs agree and $d = \deg D = \deg N + 1$ is even, as $N$ is odd.
If $F \to \infty$ at both ends, the signs agree and $d = \deg N = \deg D + 1$ is even, as $D$ is odd. $\square$

In the first case $F(x) = 1$ has a positive solution, and either it or the corresponding solution $1/x$ for the reversed orientations is at least $1$.
Note that $d$ is the degree of $N - D$, not of the minimal polynomial of a proportion; the link with the table of degrees in [results.md](results.md) remains heuristic.

## 3. Wide rectangles

### 3.1 From a network back to a tiling

A *plane network* is a network with a fixed embedding in the plane in which both poles lie on the outer face.
Let $G^+$ be the plane graph obtained by adding an edge $e_0$ from $t$ to $s$ inside the outer face.
For an edge $e$ with a direction, $\operatorname{left}(e)$ and $\operatorname{right}(e)$ are the faces of $G^+$ on its two sides.
Put $f_R = \operatorname{left}(e_0)$ and $f_L = \operatorname{right}(e_0)$.

**Lemma 3.1.** Let $(\varphi, i)$ be a flow of value $I$ on a plane network.
There is a function $\psi$ on the faces of $G^+$, unique up to an additive constant, with $\psi(\operatorname{left}(e)) - \psi(\operatorname{right}(e)) = i_e$ for every edge of $G$ in its reference direction, and $\psi(f_R) - \psi(f_L) = I$.

*Proof.*
Put $j_e = i_e$ on $G$ and $j_{e_0} = I$; by the law of Kirchhoff $j$ is a circulation on $G^+$.
The map $\partial$ that sends a function $\psi$ on the faces to the function $e \mapsto \psi(\operatorname{left}(e)) - \psi(\operatorname{right}(e))$ on the edges takes values in the circulations, because around a vertex the contributions telescope.
Its kernel is the constants, because the dual graph is connected.
By Euler's formula the space of circulations of the connected plane graph $G^+$ has dimension $|E^+| - |V| + 1$, one less than the number of faces, so $\partial$ maps onto it. $\square$

**Theorem 3.2 (Brooks, Smith, Stone and Tutte).** Let $\mathfrak N$ be a plane network with real positive resistances, and $(\varphi, i)$ a flow of value $I > 0$ in which no current $i_e$ is zero.
Direct every edge so that $i_e > 0$, and let $\psi$ be as in Lemma 3.1.
Then the rectangles
$$\operatorname{rect}(e) = [\psi(\operatorname{right}(e)), \psi(\operatorname{left}(e))] \times [\varphi(e^+), \varphi(e^-)], \qquad e \in E,$$
form a tiling of $[\psi(f_L), \psi(f_R)] \times [\varphi(t), \varphi(s)]$ by $|E|$ tiles, and $\operatorname{rect}(e)$ has width $i_e$ and height $r_e i_e$.

*Status.* Classical; this is the converse half of the correspondence of Brooks, Smith, Stone and Tutte (1940).
The proof below is complete given three standard facts: Euler's formula, used in Lemma 3.1; the Jordan curve theorem; and the duality between bonds and cycles of a connected plane graph (Diestel, *Graph Theory*, Section 4.6: a set of edges is a minimal cut exactly when the dual edges form a cycle of the dual graph).
Embeddings are taken to be piecewise linear, so that the two sides of a closed curve are well defined, and the dual of a plane graph is a multigraph, in which a minimal cut of two edges gives a cycle of length two.
The proof uses the oriented form of the duality: if the edges of a minimal cut are all directed from one side of the cut to the other, they all cross the dual cycle in the same sense; this follows from the unoriented statement, since the dual cycle separates the two sides of the cut by the Jordan curve theorem.

*Proof.*
By the law of Ohm, $\varphi$ decreases strictly along every directed edge, so the directions are acyclic.
By Lemma 2.2, $\varphi$ is largest at $s$ and smallest at $t$, so no edge enters $s$ or leaves $t$.
A vertex $v$ other than the poles has an edge, and by the law of Kirchhoff the currents entering it and those leaving it have equal sums, so it has both an entering and a leaving edge.
Following entering edges backwards from any vertex therefore leads to $s$, and following leaving edges leads to $t$.

Let $c \in (\varphi(t), \varphi(s))$ be different from every value of $\varphi$, let $U_c$ be the set of vertices with $\varphi > c$ and $D_c$ its complement.
A directed path from $s$ to a vertex of $U_c$ stays in $U_c$, so $U_c$ induces a connected subgraph; so does $D_c$.
Let $E_c$ be the set of edges of $G$ between the two; every one of them is directed from $U_c$ to $D_c$, and $E_c = \{e : \varphi(e^+) < c < \varphi(e^-)\}$.
In $G^+$ the set $E_c \cup \{e_0\}$ is a cut both of whose sides are connected, hence a minimal cut.
By duality there is a closed curve $\gamma$ that passes through distinct faces $f_0, f_1, \dots, f_{m-1}$ of $G^+$ in cyclic order, meets $G^+$ only in one interior point of each edge of the cut, and crosses these edges one at a time.
By the Jordan curve theorem $\gamma$ separates the plane into two regions; the connected sets $U_c$ and $D_c$ lie in different ones, since an edge of the cut crosses $\gamma$ once.
Traverse $\gamma$ with $U_c$ on the left.
Each edge $e \in E_c$ runs from the left of $\gamma$ to its right, so $\gamma$ crosses it from $\operatorname{right}(e)$ to $\operatorname{left}(e)$, and $\psi$ increases by $i_e$ at the crossing.
The edge $e_0$ runs from the right of $\gamma$ to its left, so $\gamma$ crosses it from $\operatorname{left}(e_0) = f_R$ to $\operatorname{right}(e_0) = f_L$.
Starting after that crossing, $\gamma$ visits $f_L = f_0, f_1, \dots, f_{m-1} = f_R$ and crosses the edges $e_1, \dots, e_{m-1}$ of $E_c$, with $[\psi(f_{j-1}), \psi(f_j)]$ the horizontal extent of $\operatorname{rect}(e_j)$.
So the rectangles that meet the horizontal line at height $c$ are those of $E_c$, and their sections subdivide the segment $[\psi(f_L), \psi(f_R)] \times \{c\}$.

This holds for all but finitely many $c$.
Every rectangle meets such a line, so it lies in the main rectangle.
Two rectangles whose interiors met would have overlapping sections on such a line.
The union of the rectangles is closed and contains every point of the main rectangle at such a height, hence all of it. $\square$

**Lemma 3.3 (duality).** Let $\mathfrak N$ be a plane network in which $G^+$ has no bridge.
Let $\mathfrak N^*$ be the network whose vertices are the faces of $G^+$, with an edge $e^*$ joining $\operatorname{left}(e)$ and $\operatorname{right}(e)$ for every edge $e$ of $G$, and with poles $f_R$ and $f_L$.
Then $\mathfrak N^*$ is a plane network, and for every orientation vector $\varepsilon$, $Z_{\mathfrak N^*, -\varepsilon} = 1/Z_{\mathfrak N, \varepsilon}$.
Moreover, for real positive resistances $r$ on $\mathfrak N$ and $1/r$ on $\mathfrak N^*$, the current in $e^*$ for a flow on $\mathfrak N^*$ vanishes exactly when the current in $e$ for a flow on $\mathfrak N$ does: by the construction in the proof, the current in $e^*$ is a non-zero multiple of the potential difference across $e$, which is $r_e$ times the current in $e$.

*Proof.*
$\mathfrak N^*$ is the dual of $G^+$ with the edge dual to $e_0$ removed, that is the dual of the plane graph $G^+/e_0$; it is connected, it has no loop because $G^+$ has no bridge, and its poles lie on the face that corresponds to the vertex of $G^+/e_0$ made of $s$ and $t$.
Let $(\varphi, i)$ be a flow of value $I$ on $\mathfrak N$ for positive resistances $r$, and $\psi$ as in Lemma 3.1.
On $\mathfrak N^*$ take the potential $\psi$ and the current $r_e i_e = \varphi(e^-) - \varphi(e^+)$ in $e^*$, directed from $\operatorname{left}(e)$ to $\operatorname{right}(e)$.
The law of Ohm holds with resistance $1/r_e$.
The law of Kirchhoff at a face says that the differences of $\varphi$ along the edges of its boundary, other than $e_0$, add up to zero, or to $\pm(\varphi(s) - \varphi(t))$ for the two faces at $e_0$; this holds because the boundary is a closed walk.
So this is a flow of value $\varphi(s) - \varphi(t)$ on $\mathfrak N^*$ with difference of potential $I$ between the poles, and the impedance of $\mathfrak N^*$ is the inverse of that of $\mathfrak N$.
This holds for all $x > 0$, hence as an identity of rational functions. $\square$

### 3.2 The set of functions

For a network with an orientation vector, the current $i_e$ of the flow of value $1$ is a rational function of $x$, by Cramer's rule.

**Definition 3.4.** A pair $(\mathfrak N, \varepsilon)$ of a plane network with $n$ edges and an orientation vector is *proper* if no current $i_e$ vanishes identically as a function of $x$.
$\mathcal F_n$ is the set of functions $Z_{\mathfrak N, \varepsilon}$ for proper pairs with $n$ edges.

**Proposition 3.5.**

1. $\mathcal F_n$ is finite, closed under $F \mapsto 1/F$, and $F \ne 1/F$ for every $F \in \mathcal F_n$. So $|\mathcal F_n|$ is even; put $E(n) = |\mathcal F_n|/2$.
2. If $\tau$ is a tiling of $[0,W] \times [0,H]$ by $n$ tiles of proportion $x$, with orientations $\varepsilon$, then $(\mathfrak N(\tau), \varepsilon)$ is proper and $Z_{\mathfrak N(\tau),\varepsilon}(x) = H/W$.
3. If $(\mathfrak N, \varepsilon)$ is proper, then for every $x > 0$ at which no current vanishes, in particular for all but finitely many $x$, there is a tiling of a rectangle of width $1$ and height $Z_{\mathfrak N,\varepsilon}(x)$ by $n$ tiles in which the tile of the edge $e$ has height $x^{\varepsilon_e}$ times its width.

*Proof.*
(1) There are finitely many networks with $n$ edges up to isomorphism, and the function depends only on the network.
A bridge of $G^+$ carries no current: its removal leaves both poles in one component, as they are joined by $e_0$, and the sum of the law of Kirchhoff over the other component is the current in the bridge.
So $G^+$ has no bridge when the pair is proper, and Lemma 3.3 applies and shows that the dual pair is proper.
$F = 1/F$ would give $F^2 = 1$, which is impossible for an odd function.
(2) is Proposition 2.4, with the remark that the currents are the widths of the tiles, which are not zero.
(3) is Theorem 3.2 with $I = 1$. $\square$

By (2) and (3), $\mathcal F_n$ is also the set of functions $Z_{\mathfrak N(\tau), \varepsilon}$ over all tilings $\tau$ by $n$ tiles of a common proportion.
Indeed, for a proper pair, (3) gives a tiling $\tau_x$ for all but finitely many $x \ge 1$; the networks $\mathfrak N(\tau_x)$, with their edges labelled by those of $\mathfrak N$, take finitely many values, so one of them occurs for infinitely many $x$, and by (2) its function agrees with $Z_{\mathfrak N,\varepsilon}$ at these $x$, hence everywhere.

It is essential that pairs with an identically vanishing current are left out.
For the network of the pinwheel of five tiles with all orientations equal, the current in the central edge vanishes identically and the function is $x$ or $1/x$.
This function does not belong to $\mathcal F_5$: by step (d) of Proposition 5.1 a proper pair would give a tiling of the rectangle $1009 \times 1$ by five tiles of proportion $1009$, and the search finds none (`rectiling --list 5 1009 1`).
This exclusion therefore rests on a computation; it is confirmed by a direct enumeration of all networks with five edges.

### 3.3 The theorem

For $w > 0$, let $X_n(w)$ be the set of $x \ge 1$ for which the rectangle $[0,w] \times [0,1]$ has a tiling by $n$ tiles of proportion $x$.
By Theorem 2.6 (5), each $F \in \mathcal F_n$ tends to $\infty$ or to $0$ at infinity; let $\mathcal F_n^\infty$ be the set of those of the first kind.
Inversion exchanges the two kinds, so $|\mathcal F_n^\infty| = E(n)$.

**Theorem 3.6.** For every $n$ there is $W(n)$ such that, for every real $w > W(n)$:

1. every $F \in \mathcal F_n^\infty$ has exactly one solution $x_F(w)$ of $F(x) = w$ in $[1, \infty)$;
2. $F \mapsto x_F(w)$ is a bijection from $\mathcal F_n^\infty$ onto $X_n(w)$.

In particular $|X_n(w)| = E(n)$.

*Status.* Proved, with $E(n)$ as in Proposition 3.5 and on the basis of Theorem 3.2.
Rationality of $w$ plays no role.

*Proof.*
Each $F \in \mathcal F_n$ is continuous on $[1,\infty)$ by Theorem 2.6 (2).

(a) If $F \in \mathcal F_n \setminus \mathcal F_n^\infty$ then $F$ is bounded on $[1,\infty)$, by $\beta_F$ say.

(b) If $F \in \mathcal F_n^\infty$ then $F(x)/x \to c_\infty > 0$ and $F'(x) \to c_\infty$, as for any rational function.
So there is $X_F \ge 1$ such that $F$ is strictly increasing on $[X_F, \infty)$.
For $X \ge X_F$ put $\mu_F(X) = \max_{[1,X]} F$.
If $w > \mu_F(X)$ then $F(x) = w$ has exactly one solution in $[1,\infty)$, and it is larger than $X$.

(c) If $F \ne G$ in $\mathcal F_n^\infty$, the two agree at finitely many points; let $X_{FG} \ge X_F$ exceed all of them.
If $w > \mu_F(X_{FG})$ and $w > \mu_G(X_G)$ then $x_F(w) \ne x_G(w)$.

(d) For $F \in \mathcal F_n^\infty$ choose a proper pair $(\mathfrak N, \varepsilon)$ with $Z_{\mathfrak N,\varepsilon} = 1/F$, which exists by Proposition 3.5 (1), and let $X'_F \ge X_F$ exceed every positive zero of its currents.
If $w > \mu_F(X'_F)$ then no current vanishes at $x = x_F(w)$, and Proposition 3.5 (3) gives a tiling of a rectangle of width $1$ and height $1/w$ by $n$ tiles of proportion $x$.
Scaling by $w$ shows that $x_F(w) \in X_n(w)$.

(e) Let $x \in X_n(w)$, and let $\tau$ be a tiling of $[0,w] \times [0,1]$ with orientations $\varepsilon$.
By Proposition 3.5 (2) and (1), $F = 1/Z_{\mathfrak N(\tau),\varepsilon}$ belongs to $\mathcal F_n$ and $F(x) = w$.
If $w$ exceeds every $\beta_F$ of (a), then $F \in \mathcal F_n^\infty$, and $x = x_F(w)$ by (b).

Let $W(n)$ be the largest of the finitely many bounds in (a) to (d). $\square$

The same proof applies to guillotine tilings, with $\mathcal F_n$ replaced by the set $\mathcal G_n$ of Section 6.2; step (d) is then immediate, since a guillotine tiling exists for every $x > 0$.
So the number of proportions of guillotine tilings of a wide rectangle is $|\mathcal G_n|/2$, which is A338781$(n)$ by Proposition 6.4.

## 4. Rational proportions that need both orientations

A tiling of the unit square by tiles of proportion $x$ that are all wide becomes, when heights are multiplied by $x$, a dissection of the rectangle $[0,1] \times [0,x]$ into squares, and conversely.
So $x \in S(n)$ is realised with one orientation exactly when a rectangle of sides $x$ and $1$ can be dissected into $n$ squares.

### 4.1 The three proportions occur

**Proposition 4.1.** $n - 4 \in S(n)$ for $n \ge 6$, $n - 11/2 \in S(n)$ for $n \ge 7$, and $n - 19/3 \in S(n)$ for $n \ge 8$.

*Status.* Proved in full.

*Proof.*
Let $m = n - 4$.
The rectangle $m \times 1$ is cut into $m$ unit squares.
The rectangle $(2m - 3) \times 2$ is cut into $m - 2$ squares of side $2$ and two of side $1$, for $m \ge 3$.
The rectangle $(3m - 7) \times 3$ is cut into $m - 3$ squares of side $3$, one of side $2$ and two of side $1$, for $m \ge 4$.
So $m$, $m - 3/2$ and $m - 7/3$ belong to $S(m)$ in the respective ranges, and they exceed $1$.
By the step of four of Theorem 1.1 they belong to $S(m + 4)$. $\square$

### 4.2 They cannot be realised with one orientation

**Lemma 4.2.** A square cannot be dissected into five squares.

*Proof.*
Each corner of the unit square lies in exactly one of the squares, and no square contains two corners.
Let $A$, $B$, $C$, $D$ be the squares at the corners, in order around the square from the bottom-left corner, of sides $a$, $b$, $c$, $d$, and let $Q$ be the fifth.
A square that has a segment in common with two sides of the unit square contains a corner or has side $1$, so $Q$ has a segment in common with at most one side, say not with the bottom, right or top side.
Each of these three sides is then covered by its two corner squares, so $a + b = b + c = c + d = 1$.
Hence $c = a$ and $d = b$, so $a + d = 1$ and the left side is covered by $A$ and $D$ as well.
$A = [0,a]^2$ and $C = [1-a,1]^2$ have disjoint interiors, so $a \le 1/2$; likewise $b \le 1/2$.
So $a = b = 1/2$, the four corner squares fill the unit square, and there is no room for $Q$. $\square$

The next two lemmas rest on one identity.
Let a rectangle $[0,L] \times [0,H]$ be dissected into $k$ squares of sides $s_1, \dots, s_k$, and for $u \in [0,L]$, not the abscissa of a corner, let $h(u) = \sum 1/s_i$ over the squares that the vertical line at $u$ crosses.
Since the $i$-th square is crossed for $u$ in an interval of length $s_i$,
$$k = \int_0^L h(u)\, \mathrm du. \tag{4.1}$$
The squares crossed by one line have sides that add up to $H$; if there are $m$ of them, then $h(u) \ge m^2/H$ by the inequality between the arithmetic and harmonic means.

**Lemma 4.3.** Let a rectangle $[0,L] \times [0,1]$ be dissected into $n$ squares, $f$ of which have side $1$.
Then there is a dissection of $[0, L - f] \times [0,1]$ into $n - f$ squares of side less than $1$, and $n - f \ge 4(L - f)$.

*Proof.*
A square of side $1$ occupies a full column, so the squares of side $1$ cut the rectangle into rectangles of height $1$, each of which is dissected by the squares it contains.
Pushing these together gives the dissection.
In it every vertical line crosses at least two squares, so $h \ge 4$, and (4.1) gives the inequality. $\square$

**Lemma 4.4.** A rectangle of sides $3$ and $2$ cannot be dissected into seven squares of side less than $2$.

*Proof.*
Take $L = 3$ and $H = 2$, and let $d(u) = h(u) - 2$.
Every line crosses at least two squares, so $d \ge 0$, and by (4.1) $\int_0^3 d = 1$.
A line is of *type a* if it crosses two squares of side $1$, where $d = 0$; of *type b* if it crosses two squares of sides $\sigma > 1$ and $2 - \sigma$, where $d = \delta(\sigma) := 2/(\sigma(2-\sigma)) - 2$; and of *type c* if it crosses at least three squares, where $d \ge 9/2 - 2 = 5/2$.
The lines of type c therefore have total length at most $2/5$.
Call a square *big* if its side exceeds $1$.
No line crosses two big squares, so the horizontal extents of the big squares do not overlap, and there are at most two of them.
A line of type a crosses a square of side $1$ that touches the bottom side; the extent of such a square has length $1$ and does not overlap the extent of a big square.
Put $\psi(\sigma) = \sigma\,\delta(\sigma) = 2(\sigma - 1)^2/(2 - \sigma)$.

*No big square.* Every line is of type a or c, so the lines of type a have total length at least $13/5$.
Each crosses two squares of side $1$, and a square of side $1$ is crossed over a length $1$, so there are at least $26/5$, hence six, squares of side $1$.
Their area is $6$, which leaves no room for the seventh square.

*One big square*, of side $\sigma$.
The lines through it are of type b or c, so $1 \ge \sigma \min(\delta(\sigma), 5/2)$; as $\sigma > 1$ this gives $\psi(\sigma) \le 1$, that is $\sigma \le 3/2$.
The lines outside its extent are of type a or c, so those of type a have total length at least $3 - \sigma - 2/5 \ge 11/10$.
But the complement of the extent consists of at most two intervals of total length $3 - \sigma < 2$, so it contains the extent of at most one square of side $1$ touching the bottom side, and the lines of type a have total length at most $1$.

*Two big squares*, of sides $\sigma_1$ and $\sigma_2$.
The complement of their extents has length $3 - \sigma_1 - \sigma_2 < 1$, so it contains no line of type a, and all its lines are of type c.
Hence $1 \ge \sum_j \sigma_j \min(\delta(\sigma_j), 5/2) + \tfrac52 (3 - \sigma_1 - \sigma_2)$.
With $v = 2 - \sigma$, $\psi(\sigma) - \tfrac52\sigma = 2/v + \tfrac92 v - 9 \ge -3$, with equality at $v = 2/3$; so $\sigma \min(\delta(\sigma), 5/2) \ge \tfrac52 \sigma - 3$ in all cases.
The right-hand side is therefore at least $\tfrac{15}{2} - 6 = \tfrac32$, a contradiction. $\square$

**Lemma 4.5.** A rectangle of sides $5$ and $3$ cannot be dissected into eight squares of side less than $3$.

*Proof.*
Take $L = 5$ and $H = 3$, and suppose that such a dissection exists.
Call a square *lower* if it touches the bottom side, *upper* if it touches the top side, and *middle* otherwise; no square is both lower and upper.
A vertical line that avoids the corners crosses one lower square, of side $\sigma$, one upper square, of side $\tau$, and possibly middle squares, of sides $c_i$; and $1/\sigma + 1/\tau \ge 4/(\sigma + \tau) \ge 4/3$.
By (4.1), $8 \ge 5 \cdot \tfrac43 + \int \sum_i 1/c_i$, and the integral is the number of middle squares, so there is at most one.
A *cut* is a vertical line, other than the two sides, that crosses the interior of no square; the cuts divide the rectangle into *blocks*, each dissected by the squares it contains.

*Blocks without a middle square.*
Every line crosses a lower and an upper square with $\sigma + \tau = 3$.
Where the lower square changes, inside the block, the upper square does not, as the line is not a cut; so consecutive lower squares have the same side, and likewise the upper ones.
The block thus consists of $a$ lower squares of side $\sigma$ and $b$ upper squares of side $3 - \sigma$ with $a\sigma = b(3 - \sigma)$, and $a$ and $b$ are coprime, as otherwise there would be a cut inside.
It has $a + b$ squares and width $3ab/(a+b)$: the widths are $3/2$ for two squares, $2$ for three, $9/4$ for four, $12/5$ or $18/5$ for five, $5/2$ for six, $18/7$, $30/7$ or $36/7$ for seven, and $21/8$ or $45/8$ for eight.

*No middle square.*
The numbers of squares of the blocks form a partition of $8$ into parts at least $2$, and the widths add up to $5$.
The partitions $8$; $6 + 2$; $5 + 3$; $4 + 4$; $4 + 2 + 2$; $3 + 3 + 2$; $2 + 2 + 2 + 2$ give the total widths $21/8$ or $45/8$; $4$; $22/5$ or $28/5$; $9/2$; $21/4$; $11/2$; $6$, none of which is $5$.

*One middle square* $M$, of side $c$.
The lines through $M$ cross three squares, so $h \ge 3$ on a length $c$, and (4.1) gives $8 \ge \tfrac{20}{3} + \tfrac53 c$, that is $c \le 4/5$.
On these lines the lower squares have their top at the bottom of $M$ and the upper squares their bottom at its top; so the lower squares below $M$ have a common side $\sigma$, the upper squares above $M$ a common side $\tau^*$, and $\sigma + c + \tau^* = 3$.
Let the block that contains $M$ have width $\omega$ and $k$ squares, and let it be $[0,\omega] \times [0,3]$, with $M$ above $[x_M, x_M + c]$.
The other blocks have no middle square, so their numbers of squares form a partition of $8 - k$ into parts at least $2$.
Below it is shown that $k \ge 4$; hence $(k, \omega)$ is one of $(8, 5)$, $(6, 7/2)$, $(5, 3)$, $(4, 11/4)$ and $(4, 2)$.

Suppose $x_M > 0$.
To the left of $M$ the lines cross two squares, and as before all lower squares there have one side $\sigma_L$ and all upper squares the side $3 - \sigma_L$.
The line at $x_M$ is not a cut, so it crosses the interior of a lower or an upper square.
If of a lower one, then $\sigma_L = \sigma$; if of an upper one, then $3 - \sigma_L = \tau^*$; these exclude each other because $c > 0$.
So exactly one of the two kinds of square straddles the line at $x_M$, and the squares of the other kind end there.
The same holds at $x_M + c$ if $x_M + c < \omega$.
Up to the reflections of the rectangle in its two axes, four cases remain.

*(i) $x_M = 0$ and $x_M + c = \omega$.*
Then $c = a\sigma = b\tau^*$ with integers $a, b \ge 1$, so $3 = c(1 + 1/a + 1/b) \le 3c$, contrary to $c \le 4/5$.

*(ii) $x_M = 0$, and a lower square straddles the line at $c$.*
All $p$ lower squares have side $\sigma = \omega/p$; $a \ge 1$ upper squares lie above $M$; and $b \ge 1$ upper squares of side $3 - \sigma$ fill the rest, so $c = \omega - b(3 - \sigma) = \omega(1 + b/p) - 3b$, with $k = p + a + b + 1$ and $p + b \le k - 2$.
For $k = 4$: $c = 2\omega - 3 \ge 1$.
For $(k,\omega) = (5,3)$: $c = 3 - 3b(p-1)/p \ge 3/2$, as $p + b \le 3$.
For $(6, 7/2)$: $c = \tfrac72 + b(\tfrac{7}{2p} - 3)$, which for $p + b \le 4$ is at least $1$.
For $(8, 5)$: $c = 5 - b(3 - 5/p)$, which for $p + b \le 6$ is at least $1$.
All contradict $c \le 4/5$.

*(iii) $0 < x_M$, $x_M + c < \omega$, and lower squares straddle both lines.*
All $p$ lower squares have side $\sigma = \omega/p$; $a \ge 1$ upper squares lie above $M$, and $t \ge 2$ upper squares of side $3 - \sigma$ lie to its left and right, so $c = \omega(1 + t/p) - 3t$, with $k = p + a + t + 1$ and $p + t \le k - 2$.
For $(5,3)$: $c = 3$.
For $(6, 7/2)$: $c \ge 1$.
For $(8,5)$: $c = 5 + t(5/p - 3)$, which for $p + t \le 6$ is at least $1$.
All contradict $c \le 4/5$.

*(iv) $0 < x_M$, $x_M + c < \omega$, a lower square straddles the line at $x_M$ and an upper square the line at $x_M + c$.*
From the left, there are $a$ lower squares of side $\sigma$, ending at $x_M + c$, then $b$ lower squares of side $3 - \tau^* = \sigma + c$; and $a'$ upper squares of side $3 - \sigma$, ending at $x_M$, then $b'$ upper squares of side $\tau^* = 3 - \sigma - c$.
So $k = a + b + a' + b' + 1$ and
$$(a + b)\sigma + bc = \omega, \qquad (a' + b')(3 - \sigma) - b'c = \omega, \qquad a\sigma - c = a'(3 - \sigma).$$
The rotation of the rectangle by a half-turn exchanges $(a, b, a', b')$ with $(b', a', b, a)$.
For $(5, 3)$, all four numbers are $1$, and the first and third equations give $c = 0$.
For $(6, 7/2)$, up to the half-turn $(a,b,a',b')$ is $(2,1,1,1)$ or $(1,2,1,1)$: the first and third equations give $(\sigma, c) = (13/12, 1/4)$, which violates the second, and $(19/14, -2/7)$.
For $(8, 5)$, $a + b + a' + b' = 7$; up to the half-turn $a + b \le 3$.
If $a + b = 2$, the first equation gives $\sigma \ge (5 - 4/5)/2 > 2$ and the second $5(3 - \sigma) > 5$, a contradiction.
If $a + b = 3$, the first and third equations give, for $(a, b; a', b')$ equal to $(1,2;1,3)$, $(1,2;2,2)$, $(1,2;3,1)$, $(2,1;1,3)$, $(2,1;2,2)$ and $(2,1;3,1)$, the values $(\sigma, c) = (11/7, 1/7)$, $(17/9, -1/3)$, $(23/11, -7/11)$, $(4/3, 1)$, $(11/7, 2/7)$ and $(7/4, -1/4)$.
Three have $c < 0$; for the others the left-hand side of the second equation is $37/7$, $11/3$ and $36/7$, not $5$.

In the cases (ii) to (iv) the block has at least four squares, as was used above. $\square$

The arithmetic of this proof was repeated by a script over all values of the parameters, with the same outcome.
Independently, the exhaustive search finds that the rectangle $5 \times 3$ cannot be dissected into eight squares at all: `rectiling --list --minority 0 8 5 3` reports no proportion equal to $1$, with no singular or constant case.

**Theorem 4.6.**

1. For $n \ge 5$, a rectangle of sides $n - 4$ and $1$ cannot be dissected into $n$ squares.
2. For $n \ge 6$, a rectangle of sides $n - 11/2$ and $1$ cannot be dissected into $n$ squares.
3. For $n \ge 7$, a rectangle of sides $n - 19/3$ and $1$ cannot be dissected into $n$ squares.

*Status.* Proved in full, by hand; the finite facts on which it rests, Lemmas 4.2, 4.4 and 4.5, agree with the exhaustive search.

*Proof.*
Suppose that the rectangle $L \times 1$ is dissected into $n$ squares, and apply Lemma 4.3: there is a dissection of $\ell \times 1$ into $k$ squares of side less than $1$, where $\ell = L - f$ and $k = n - f$, so that $k - \ell = n - L$, and $k \ge 4\ell$.

(1) Here $k - \ell = 4$ and $\ell$ is an integer, so $4\ell \le \ell + 4$ gives $\ell \le 1$.
If $\ell = 0$ then $k = 0$, which contradicts $k - \ell = 4$.
If $\ell = 1$ then $k = 5$, which contradicts Lemma 4.2.

(2) Here $k = \ell + 11/2$, so $\ell \le 11/6$ and $\ell - 1/2$ is an integer: $\ell = 1/2$ or $\ell = 3/2$.
If $\ell = 1/2$ then $k = 6$, and the rectangle $2 \times 1$ would be dissected into six squares, contrary to (1) for $n = 6$.
If $\ell = 3/2$ then $k = 7$, and the rectangle $3 \times 2$ would be dissected into seven squares of side less than $2$, contrary to Lemma 4.4.

(3) Here $k = \ell + 19/3$, so $\ell \le 19/9$ and $\ell - 2/3$ is an integer: $\ell = 2/3$ or $\ell = 5/3$.
If $\ell = 2/3$ then $k = 7$, and the rectangle $3 \times 2$ would be dissected into seven squares, contrary to (2) for $n = 7$.
If $\ell = 5/3$ then $k = 8$, and the rectangle $5 \times 3$ would be dissected into eight squares of side less than $3$, contrary to Lemma 4.5. $\square$

So, for $n \ge 8$, the proportions $n - 4$, $n - 11/2$ and $n - 19/3$ belong to $S(n)$ and are realised only by tilings with both orientations.

**Remark 4.7.** The same argument shows that $m$, $m - 3/2$ and $m - 7/3$ are the three largest $L$ for which $L \times 1$ can be dissected into $m$ squares, for $m \ge 4$.
Indeed, if $0 < m - L < 7/3$ then $\ell < 7/9$ and $k = \ell + (m - L) < 28/9$, so $k \le 3$.
Two squares of side less than $1$ tile $\ell \times 1$ only for $\ell = 1/2$, which gives $m - L = 3/2$.
Three such squares do so only for $\ell = 1/3$ and $\ell = 2/3$: one of them contains a left and a right corner, so it has side $\ell$, and the other two tile a rectangle of sides $\ell$ and $1 - \ell$, one of which is then twice the other.
These give $m - L = 8/3$ and $7/3$.

### 4.3 Exhaustiveness, and the exceptions for small $n$

**Conjecture 4.8.** For $n \ge 10$, every rational element of $S(n)$ other than $n - 4$, $n - 11/2$ and $n - 19/3$ is realised with one orientation.

*Status.* Open.
It holds for $10 \le n \le 13$ by computation.
No argument is known that would bound the rational proportions of tilings with both orientations, and no general construction is known that adds four squares to a dissection into squares, which is what would be needed to realise with $n$ squares the remaining rational elements of $S(n-4)$.

For $6 \le n \le 9$, Proposition 4.1 and Theorem 4.6 account for all entries of the table of the analysis except two, since $n - 11/2 > 1$ requires $n \ge 7$ and $n - 19/3 > 1$ requires $n \ge 8$.
The two others are sporadic: they come from pinwheels whose central rectangle is not a square.

- $5/3 \in S(6)$. In a square of side $105$: a wide tile $75 \times 45$ at the bottom-left, a tall tile $30 \times 50$ at the bottom-right, a tall tile $33 \times 55$ at the top-right, two tall tiles $36 \times 60$ side by side at the top-left, and a tall tile $3 \times 5$ in the centre.
- $16/5 \in S(9)$. In a square of side $3040$: a wide tile $2560 \times 800$ at the bottom-left, a tall tile $480 \times 1536$ at the bottom-right, two tall tiles $470 \times 1504$ at the top-right, three tall tiles $700 \times 2240$ at the top-left, and two tall tiles $230 \times 736$ in the centre.

The rectangles $5 \times 3$ and $16 \times 5$ cannot be dissected into six and nine squares respectively, by the search.
Why no such sporadic proportion occurs for $10 \le n \le 13$ is not explained.

## 5. The threshold width

**Proposition 5.1.** Theorem 3.6 holds with $W(n) = n\,(1 + 4^n/2)$.

*Status.* Proved here assuming Kirchhoff's formulas for a network with conductances $y$ (Kirchhoff 1847; for the general form, the all-minors matrix-tree theorem of Chaiken 1982):

- $\det L_t = \sum_T \prod_{e \in T} y_e$ over the spanning trees $T$ of $G$;
- $\det L_{st} = \sum_\Phi \prod_{e \in \Phi} y_e$ over the spanning forests $\Phi$ with two components, one containing each pole;
- for the flow of value $1$, $i_e \det L_t = \sum_T \pm \prod_{f \in T} y_f$ over the spanning trees $T$ that contain $e$ and whose path between the poles passes through $e$.

*Proof.*
Let $(\mathfrak N, \varepsilon)$ be a pair with $n$ edges, $m$ of them of orientation $-1$, and $F = Z_{\mathfrak N,\varepsilon} = N/D$ in lowest terms.
Multiply the three sums by $x^m \prod_e r_e$: this gives polynomials $\tilde P$, $\tilde Q$ and $\nu_e$ in $x$ with $F = \tilde P/\tilde Q$ and $i_e = \nu_e/\tilde Q$, where $\tilde P$ and $\tilde Q$ have non-negative integer coefficients.
$\tilde Q(1)$ is the number of spanning trees, at most $\binom{n}{|V|-1}$; $\tilde P(1)$ is at most $\binom{n}{|V|-2}$; and the sum of the absolute values of the coefficients of $\nu_e$ is at most $\tilde Q(1)$.
Each binomial coefficient is at most $\binom{n}{\lfloor n/2 \rfloor} \le 2^{n-1}$.
Write $\tilde P = gN$ and $\tilde Q = gD$.
Then $g \in \mathbb Z[x]$: write $g = (a/b)\,g_0$ with $g_0 \in \mathbb Z[x]$ primitive and $a/b$ a fraction in lowest terms; by Gauss's lemma $b$ divides the content of $N$ and that of $D$, which have no common factor since $N/D$ is in lowest terms over $\mathbb Z$, so $b = 1$.
The roots of $g$ are roots of $\tilde Q$, which lie on the imaginary axis, as in Theorem 2.6 (3); so $g$ has coefficients of one sign and $|g(1)| \ge 1$.
Hence $N(1) \le 2^{n-1}$ and $D(1) \le 2^{n-1}$, and these bound every coefficient of $N$ and $D$.
A root $z$ of a polynomial with integer coefficients $a_0, \dots, a_d$, $a_d \ne 0$, satisfies $|z| < 1 + \max_j |a_j|$ (Cauchy's bound).
By Lemma 2.2, every $F \in \mathcal F_n$ satisfies $F(x) \le n x$ for $x \ge 1$, because $1/F \in \mathcal F_n$ is an impedance.
Now follow the proof of Theorem 3.6 for $w > W(n)$.

(a) If $F \notin \mathcal F_n^\infty$, then $x F(x)$ is non-decreasing with limit the quotient of the leading coefficients of $N$ and $D$, at most $2^{n-1}$; so $F \le 2^{n-1} < w$ on $[1,\infty)$.

(b) Let $F \in \mathcal F_n^\infty$, and write $F(x) = c_\infty x + G(x)$ in the notation of Theorem 2.6 (6).
Then $G'(x) \ge -K/x^2$ with $K = c_0 + \sum_j 2\kappa_j = \lim x\,G(x)$, because $|\omega^2 - x^2| \le \omega^2 + x^2$.
If $N = a_d x^d + a_{d-2} x^{d-2} + \dots$ and $D = b_{d-1} x^{d-1} + \dots$, then $c_\infty = a_d/b_{d-1}$ and $K \le a_{d-2}/b_{d-1}$, so $K/c_\infty \le a_{d-2}/a_d \le 2^{n-1}$.
So $F$ is strictly increasing on $[X_0, \infty)$, where $X_0 = 2^{(n-1)/2}$.
A solution $x \ge 1$ of $F(x) = w$ satisfies $x \ge w/n > X_0$, and $F(X_0) \le n X_0 < w$; so there is exactly one solution $x_F(w)$, and $x_F(w) \ge w/n > 1 + 4^n/2$.

(c) If $F \ne G$ in $\mathcal F_n^\infty$, a common solution is a root of $N_F D_G - N_G D_F$, a non-zero polynomial with integer coefficients of absolute value at most $2 \cdot 4^{n-1}$; its roots are smaller than $1 + 4^n/2$.

(d) A zero of a current of a proper pair is a root of some $\nu_e \ne 0$, hence smaller than $1 + 2^{n-1}$.

(e) is covered by (a) and (b). $\square$

The bound is far from the truth: the counts stabilise at $w = \lfloor n^2/4 \rfloor + 2$ for $n \le 9$.

**Proposition 5.2.** Let $n \ge 2$, and let $a, b \ge 1$ be integers with $a + b = n$.
For $w = ab + 1$, two distinct functions of $\mathcal F_n^\infty$ have the common solution $x = b$ of $F(x) = w$, and $b \in X_n(w)$.
Consequently statements (1) and (2) of Theorem 3.6 do not both hold for $w = \lfloor n^2/4 \rfloor + 1$, and every $W(n)$ for which the theorem holds is at least $\lfloor n^2/4 \rfloor + 1$.

*Proof.*
Place $a$ wide tiles of height $1$ side by side, of total width $ax$, and beside them a block of $b$ tiles of height $1$ in all.
If the $b$ tiles are tall and side by side, the block has width $b/x$; if they are wide and stacked, it has width $x/b$.
The functions $ax + b/x$ and $ax + x/b$ are different, belong to $\mathcal F_n^\infty$, and take the value $ab + 1$ at $x = b$.
The largest value of $ab$ is $\lfloor n^2/4 \rfloor$. $\square$

**Conjecture 5.3.** For integers $w \ge \lfloor n^2/4 \rfloor + 2$, $|X_n(w)| = E(n)$; and $|X_n(\lfloor n^2/4 \rfloor + 1)|$ is $E(n) - 1$ for even $n$ and $E(n) - 2$ for odd $n$.

*Status.* Open.
Proposition 5.2 exhibits one coincidence for even $n$, where $a = b$, and two for odd $n$, where $(a, b)$ and $(b, a)$ give the same width.
It does not give $|X_n(w)| < E(n)$ at that width, because a function may contribute several solutions when $w$ is small.
What is missing is a proof that beyond that width no two functions share a solution, every function of $\mathcal F_n^\infty$ has one solution, the functions of the other kind have none, and no tile vanishes.
The gap between the proved width, exponential in $n$, and the conjectured one, quadratic, comes from the use of Cauchy's bound on the roots of $N_F D_G - N_G D_F$.

## 6. Upper bounds

### 6.1 All tilings

Let $M(n) = 2\,(3n)!/((2n+1)!\,(n+1)!)$.
A planar map is *non-separable* if it is connected, has no loop, and has no vertex whose removal disconnects it; the map with two vertices and two parallel edges is included.
A map is *rooted* by the choice of an edge, a direction of it and one of its sides.

**Theorem (Tutte 1963).** The number of rooted non-separable planar maps with $m \ge 2$ edges is $2\,(3m-3)!/(m!\,(2m-1)!)$; for $m = n + 1$ this is $M(n)$.

The reference is W. T. Tutte, *A census of planar maps*, Canadian Journal of Mathematics 15 (1963), 249–271; the formula was taken from secondary sources and the paper was not consulted.

**Lemma 6.1.** Let $\tau$ be a tiling of a rectangle by $n \ge 1$ tiles. Then $G^+$, for the plane network $\mathfrak N(\tau)$, is a non-separable planar map with $n + 1$ edges.

*Proof.*
Direct each edge from the top of its tile to the bottom.
The height decreases along edges, every component other than $s$ carries the bottom side of a tile, and every component other than $t$ the top side of one.
So from every vertex $v$ a directed path leads down to $t$ and one leads up from $v$ to $s$ against the directions; the first passes only through vertices lower than $v$ and the second only through higher ones.
Remove a vertex $u$.
If $u = s$, every other vertex still reaches $t$; similarly if $u = t$.
Otherwise each remaining vertex $v$ still has its path to $t$ or its path to $s$, since $u$ is not both lower and higher than $v$, and $s$ and $t$ are joined by $e_0$.
So $G^+$ has no cut vertex; it has no loop, and it has $n + 1$ edges. $\square$

**Theorem 6.2.** $a(n) \le n\,2^{n-1} M(n)$ for every $n \ge 1$.

*Status.* Proved here assuming Tutte's theorem; everything else is proved in this note.

*Proof.*
Let $x \in S(n)$ and let $\tau$ be a tiling of the unit square by $n$ tiles of proportion $x$.
Transposing if necessary, the tile at the bottom-left corner is wide; for $x = 1$ label every tile wide.
Root the map $G^+$ of $\mathfrak N(\tau)$ at $e_0$; the edge of the bottom-left tile is then the first edge after $e_0$ in the rotation at $t$, on a side fixed once and for all.
By Proposition 2.4, $Z_{\mathfrak N(\tau), \varepsilon}(x) = 1$, so $x$ is a root of $N - D$, where $N/D$ is this function in lowest terms.
By Theorem 2.6, $N - D$ is not zero and has degree at most $n$, and it depends only on the isomorphism class of the rooted map with its orientation vector.
By Lemma 6.1 and Tutte's theorem there are at most $M(n)$ rooted maps, each with at most $2^{n-1}$ orientation vectors in which the distinguished edge is wide, and each pair contributes at most $n$ roots. $\square$

Since $M(n)$ grows as $(27/4)^n n^{-5/2}$ up to a constant, the growth constant of $a(n)$ is at most $27/2$.

**Remark 6.3 (the count $T(n)$).** The analysis states the bound for $T(n)$, the number of triples of a placement sequence, an orientation vector with the first tile wide, and a proportion at which the sequence gives a tiling of the square.
The proof above bounds the number of triples of a rooted map, an orientation vector and a proportion.
The map from the first kind of triple to the second is injective provided that (i) different placement sequences belong to different mosaic classes, and (ii) a mosaic class is determined by its plane network together with the directions of the edges.
Given (ii), the class is recovered from the map, the orientations and the proportion, because the directions are those of the currents, which are determined by Lemma 2.1.
Statement (i) is asserted in [enumeration.md](enumeration.md) and listed as not proved in the Lean development.
Statement (ii) is the correspondence between mosaic classes and plane bipolar orientations, both counted by the Baxter numbers (Bonichon, Bousquet-Mélou and Fusy 2010; Felsner, Fusy, Noy and Orden 2011); it is not proved here, and the references were not consulted for the exact form needed.
So $T(n) \le n\,2^{n-1} M(n)$ is proved assuming (i) and (ii).
The correspondence also explains why $M(5) = 91$ is smaller than the number $92$ of mosaic classes: the two pinwheels of five tiles have the same network and differ in the direction of the central edge.

### 6.2 Guillotine tilings

Let $\mathcal G_1 = \{x, 1/x\}$, and let $\mathcal G_n$ be the set of the functions $A + B$ and $(A^{-1} + B^{-1})^{-1}$ with $A \in \mathcal G_j$, $B \in \mathcal G_{n-j}$ and $1 \le j < n$.
A guillotine tiling is a single tile, or two guillotine tilings on the two sides of a segment that crosses the main rectangle.
By induction, the ratio of width to height of the main rectangle of a guillotine tiling by $n$ tiles of proportion $x$ is $F(x)$ for some $F \in \mathcal G_n$, and conversely every $F \in \mathcal G_n$ and every $x > 0$ arise in this way.
Let $g(n)$ be the number of proportions of guillotine tilings of the square by $n$ tiles, and $\sigma_n$ the number of series–parallel networks with $n$ edges of two kinds, that is of expressions as above up to commutativity and associativity: $2, 6, 20, 80, 340, 1570, 7540, \dots$

**Proposition 6.4.**

1. $\mathcal G_n$ is closed under inversion without fixed point, and $|\mathcal G_n|/2$ is A338781$(n)$, half the largest number of resistances obtainable from $n$ resistors of two kinds by series and parallel combinations.
2. $g(n) \le n \cdot |\mathcal G_n|/2 \le n\,\sigma_n/2$.

*Status.* Proved in full.
In particular the resistances come in pairs, exchanged by swapping the two kinds of resistor and exchanging series with parallel, which a comment in the OEIS entry presents as unproved; the entry also links a note by David Einstein, *Proof that the maximum number of resistances is even*, so the pairing is not new.

*Proof.*
(1) $1/(A + B)$ is the harmonic sum of $1/A$ and $1/B$, so $\mathcal G_n$ is closed under inversion by induction.
Every element of $\mathcal G_n$ is the inverse of the impedance of the network of a tiling, so $F \ne 1/F$ by Theorem 2.6 (1).
The resistance of a series–parallel circuit of resistors of values $u$ and $v$ is a rational function $\rho(u, v)$, homogeneous of degree one, so $\rho(u,v) = \sqrt{uv}\,\rho(\sqrt{u/v}, \sqrt{v/u})$.
Hence $\rho$ is determined by $F(x) = \rho(x, 1/x)$, and $\rho \mapsto F$ is a bijection from the set of these functions to $\mathcal G_n$; the largest number of resistances is the number of distinct functions $\rho$, attained when $u$ and $v$ are algebraically independent.
Under this bijection $1/F$ corresponds to $uv/\rho(u,v) = 1/\rho(1/v, 1/u)$, the resistance of the circuit with series and parallel exchanged and the two kinds swapped.
(2) A proportion of a guillotine tiling of the square is a solution $x \ge 1$ of $F(x) = 1$ with $F \in \mathcal G_n$; $F$ and $1/F$ have the same solutions, and there are at most $n$ of them by Theorem 2.6 (5).
The map from expressions to functions is onto $\mathcal G_n$. $\square$

A network is a single edge, or a multiset of at least two networks joined in series, none of them itself a series composition, or the same in parallel.
So the numbers $\sigma_n$ satisfy $\prod_{j \ge 1} (1 - z^j)^{-\beta_j} = 1 + \sum_n \sigma_n z^n$ with $\beta_1 = 2$ and $\beta_j = \sigma_j/2$ for $j \ge 2$.
The quotients $\sigma_{n+1}/\sigma_n$, corrected by the factor $(1 - 3/(2n+2))^{-1}$, are $6.15881$, $6.15887$ and $6.15889$ at $n = 100$, $200$ and $399$.
So the growth constant of $g(n)$ is at most that of $\sigma_n$, numerically $6.1589$.
That $\sigma_n$ grows as a constant times $\varrho^{-n} n^{-3/2}$ is the standard behaviour of such equations and was not proved here; the value of the constant is numerical.
The lower bound $2^{n-2} \le g(n)$ of the analysis was not examined.

## 7. Remaining conjectures

- **Log-convexity of $a(n)$.** Open. It holds for $n \le 13$. Persistence gives only $a(n+3) \ge a(n)$, and no injection from $S(n) \times S(n+2)$ to $S(n+1)^2$, or comparable structure, is known.
- **$|X_n(w)| \le E(n)$ for all $w$.** Open. Theorem 3.6 gives equality for large $w$. For small $w$ a function can have several solutions and the functions of the other kind contribute as well, so the bound would have to come from coincidences and vanishing tiles, for which there is no argument. The trivial bound is $|X_n(w)| \le 2n\,E(n)$.
- **$g(n)/a(n) \to 0$.** Open. It would follow from a lower bound on the growth constant of $a(n)$ above $6.159$, by Proposition 6.4; the quotients $a(n+1)/a(n)$ reach $8.68$ at $n = 12$ and are still rising, but no lower bound on the growth of $a(n)$ beyond that of $g(n)$ is proved.

## 8. Corrections to the analysis

- *Definition of $E(n)$.* The count of functions must leave out the pairs of an arrangement and an orientation vector in which some tile vanishes identically. Such pairs exist from $n = 5$ on, and their functions need not be realised by any tiling with $n$ tiles. With all pairs included, the statement on wide rectangles would be false. Step 4 of the sketch also overlooked that a tile that does not vanish may be negative for large $x$; this is harmless only because the tiling then belongs to another arrangement with the same network, which is the content of Theorem 3.2.
- *Reversing all orientations.* It replaces $R(x)$ by $R(1/x)$, not by $1/R(x)$; the inverse $1/R$ belongs to the transposed tiling. The conclusion drawn from it, that a function of the first kind or its reversal has a solution at least $1$, is unaffected.
- *Indexing of the maps.* $M(n)$ counts the rooted non-separable planar maps with $n + 1$ edges, the additional edge joining the poles.
- *Rational proportions.* That the three rectangles cannot be cut into $n$ squares is no longer conjectural; exhaustiveness remains so.

## References

- R. L. Brooks, C. A. B. Smith, A. H. Stone, W. T. Tutte, *The dissection of rectangles into squares*, Duke Mathematical Journal 7 (1940), 312–340.
- S. Chaiken, *A combinatorial proof of the all minors matrix tree theorem*, SIAM Journal on Algebraic and Discrete Methods 3 (1982), 319–329.
- R. Diestel, *Graph Theory*, Springer, Section 4.6 (plane duality).
- R. M. Foster, *A reactance theorem*, Bell System Technical Journal 3 (1924), 259–267.
- G. Kirchhoff, *Ueber die Auflösung der Gleichungen, auf welche man bei der Untersuchung der linearen Vertheilung galvanischer Ströme geführt wird*, Annalen der Physik 72 (1847), 497–508.
- W. T. Tutte, *A census of planar maps*, Canadian Journal of Mathematics 15 (1963), 249–271.
- N. Bonichon, M. Bousquet-Mélou, É. Fusy, *Baxter permutations and plane bipolar orientations*, Séminaire Lotharingien de Combinatoire 61A (2010), B61Ah.
- S. Felsner, É. Fusy, M. Noy, D. Orden, *Bijections for Baxter families and related objects*, Journal of Combinatorial Theory A 118 (2011), 993–1020.
- OEIS Foundation, *The On-Line Encyclopedia of Integer Sequences*, sequences A000139, A210517, A338781.

Of these, only the OEIS entry A338781 and secondary statements of Tutte's formula were consulted while writing this note; the other works are cited for results that are standard, and their statements were not checked against the originals.

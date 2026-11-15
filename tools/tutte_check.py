# SPDX-License-Identifier: LGPL-3.0-or-later
"""Counts rooted non-separable planar maps by the definitions of CombinatorialMap.lean."""

import sys
from itertools import permutations
from math import factorial


def cycles(p: tuple[int, ...]) -> list[int]:
    lab = [-1] * len(p)
    c = 0
    for i in range(len(p)):
        if lab[i] < 0:
            j = i
            while lab[j] < 0:
                lab[j] = c
                j = p[j]
            c += 1
    return lab


def reach(start: int, n: int, steps) -> set[int]:
    seen = {start}
    todo = [start]
    while todo:
        a = todo.pop()
        for b in steps(a):
            if b not in seen:
                seen.add(b)
                todo.append(b)
    return seen


def valid(sigma: tuple[int, ...], alpha: tuple[int, ...]) -> bool:
    n = len(sigma)
    vert = cycles(sigma)
    if any(vert[d] == vert[alpha[d]] for d in range(n)):
        return False
    if len(reach(0, n, lambda a: (sigma[a], alpha[a]))) < n:
        return False
    face = tuple(sigma[alpha[d]] for d in range(n))
    nv = max(vert) + 1
    nf = max(cycles(face)) + 1
    if nv + nf != n // 2 + 2:
        return False
    for u in range(nv):
        rest = [d for d in range(n) if vert[d] != u]
        if not rest:
            continue
        got = reach(
            rest[0],
            n,
            lambda a: [sigma[a]] + ([alpha[a]] if vert[alpha[a]] != u else []),
        )
        if len(got) < len(rest):
            return False
    return True


def count(m: int) -> int:
    n = 2 * m
    alpha = tuple(d ^ 1 for d in range(n))
    good = sum(1 for sigma in permutations(range(n)) if valid(sigma, alpha))
    num = n * good
    den = 2**m * factorial(m)
    assert num % den == 0
    return num // den


for m in range(2, int(sys.argv[1]) + 1):
    print(m, count(m), 2 * factorial(3 * m - 3) // (factorial(m) * factorial(2 * m - 1)))

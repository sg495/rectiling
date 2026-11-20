// SPDX-License-Identifier: LGPL-3.0-or-later
// Counts rooted non-separable planar maps by the definitions of CombinatorialMap.lean (same test as tools/tutte_check.py).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, m;
static int sigma[16], alpha_[16];

static int cycles(const int *p, int *lab) {
    int c = 0;
    for (int i = 0; i < n; i++) lab[i] = -1;
    for (int i = 0; i < n; i++) {
        if (lab[i] < 0) {
            int j = i;
            while (lab[j] < 0) { lab[j] = c; j = p[j]; }
            c++;
        }
    }
    return c;
}

static int valid(void) {
    int vert[16], flab[16], face[16];
    int nv = cycles(sigma, vert);
    for (int d = 0; d < n; d++) if (vert[d] == vert[alpha_[d]]) return 0;
    for (int d = 0; d < n; d++) face[d] = sigma[alpha_[d]];
    int nf = cycles(face, flab);
    if (nv + nf != m + 2) return 0;
    // connected: reach from dart 0 by sigma and alpha
    {
        int seen[16] = {0}, stack[16], top = 0, cnt = 1;
        seen[0] = 1; stack[top++] = 0;
        while (top) {
            int a = stack[--top];
            int b = sigma[a];
            if (!seen[b]) { seen[b] = 1; cnt++; stack[top++] = b; }
            b = alpha_[a];
            if (!seen[b]) { seen[b] = 1; cnt++; stack[top++] = b; }
        }
        if (cnt < n) return 0;
    }
    for (int u = 0; u < nv; u++) {
        int start = -1, rest = 0;
        for (int d = 0; d < n; d++) if (vert[d] != u) { if (start < 0) start = d; rest++; }
        if (rest == 0) continue;
        int seen[16] = {0}, stack[16], top = 0, cnt = 1;
        seen[start] = 1; stack[top++] = start;
        while (top) {
            int a = stack[--top];
            int b = sigma[a];
            if (!seen[b]) { seen[b] = 1; cnt++; stack[top++] = b; }
            b = alpha_[a];
            if (vert[b] != u && !seen[b]) { seen[b] = 1; cnt++; stack[top++] = b; }
        }
        if (cnt < rest) return 0;
    }
    return 1;
}

static unsigned long long good;
static int used[16];

static void rec(int i) {
    if (i == n) { if (valid()) good++; return; }
    for (int v = 0; v < n; v++) {
        if (used[v]) continue;
        used[v] = 1; sigma[i] = v;
        rec(i + 1);
        used[v] = 0;
    }
}

int main(int argc, char **argv) {
    int mmax = atoi(argv[1]);
    for (m = 2; m <= mmax; m++) {
        n = 2 * m;
        for (int d = 0; d < n; d++) alpha_[d] = d ^ 1;
        good = 0;
        memset(used, 0, sizeof used);
        rec(0);
        unsigned long long den = 1;
        for (int k = 1; k <= m; k++) den *= 2ULL * k;
        unsigned long long num = (unsigned long long)n * good;
        printf("%d good=%llu classes=%llu rem=%llu\n", m, good, num / den, num % den);
        fflush(stdout);
    }
    return 0;
}

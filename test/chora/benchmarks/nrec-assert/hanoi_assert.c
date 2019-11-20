// Adapted from: https://costa.fdi.ucm.es/pubs/examples.php
#include "tick.h"
#include "chora_pow_log_helpers.h"
#include "assert.h"

static void hanoi(int n, int t, int f, int u) {
    tick(1);
    if (n > 0) {
        hanoi(n-1, u, f, t);
        hanoi(n-1, t, u, f);
    }
}

void main(int n, int t, int f, int u) {
    init_tick(0);

    hanoi(n,t,f,u);
    __VERIFIER_assume(n >= 0);

    __VERIFIER_assert(__cost <= 2 * pow2_helper(n) - 1);
}

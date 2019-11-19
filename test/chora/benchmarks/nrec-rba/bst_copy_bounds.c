// Adapted from: https://costa.fdi.ucm.es/pubs/examples.php
#include "tick.h"

void copy(int t_depth) {
    tick(1);
    int lc_depth = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= lc_depth && lc_depth <= t_depth - 1);
    int rc_depth = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= rc_depth && rc_depth <= t_depth - 1);
    __VERIFIER_assume(t_depth == lc_depth + 1 || t_depth == rc_depth + 1);

    if (lc_depth > 0) { copy(lc_depth); }
    if (rc_depth > 0) { copy(rc_depth); }
}

void main(int t_depth) {
    init_tick(0);
    __VERIFIER_assume(t_depth >= 0);

    copy(t_depth);
}

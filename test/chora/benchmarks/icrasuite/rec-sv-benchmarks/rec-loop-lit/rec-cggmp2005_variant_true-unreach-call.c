// Source: A. Costan, S. Gaubert, E. Goubault, M. Martel, S. Putot: "A Policy
// Iteration Algorithm for Computing Fixed Points in Static Analysis of
// Programs", CAV 2005

#include "assert.h"

int lo, mid, hi;

void rec() {
    if (mid > 0) {
        lo = lo + 1;
        hi = hi - 1;
        mid = mid - 1;
        rec();
    }
}

int main() {
    lo = 0;
    mid = __VERIFIER_nondet_int();
    __VERIFIER_assume(mid > 0 && mid <= LARGE_INT);
    hi = 2*mid;

    rec();
    __VERIFIER_assert(lo == hi);
    return 0;
}
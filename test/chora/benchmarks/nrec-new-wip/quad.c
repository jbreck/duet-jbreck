#include "assert.h"

int quad(int m) {
    if (m == 0) { return 0; }
    int retval;
    do {
        retval = quad(m-1) + m;
    } while(__VERIFIER_nondet_int());
    return retval;
}

void main(int n) {
    if (n >= 1 && n <= 32767) {
        __VERIFIER_assert(quad(n) * 2 == n + n * n);
    }
}

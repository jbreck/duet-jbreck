// Adapted from: https://costa.fdi.ucm.es/pubs/examples.php
#include "tick.h"
#include "chora_pow_log_helpers.h"
#include "assert.h"

int fibonacciMethod(int A){
    __VERIFIER_assume(A >= 0);
    tick(1);
    if (A <= 1){
        return 1;
    } else{
        return (fibonacciMethod(A-1)+fibonacciMethod(A-2));
    }
}

void main(int A) {
    __VERIFIER_assume(A >= 0);
    init_tick(0);

    fibonacciMethod(A);

    __VERIFIER_assert(__cost <= 2 * pow2_helper(A) - 1);
}

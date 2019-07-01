int fib(int n) {
    __VERIFIER_assume(n >= 0);
    if (n == 0 || n == 1) { return 1; }
    return fib(n-1) + fib(n-2);
}

int pow2(int n) {
    int r = 1;
    for(int i = 0; i != n; i++) {
        r = 2*r;
    }
    return r;
}

void main(int n) {
    __VERIFIER_assume(n >= 0);
    int retval = fib(n);
    int pow2n = pow2(n);
    if (__VERIFIER_nondet_int()) {
        __VERIFIER_assert(retval <= pow2n);
    }
}

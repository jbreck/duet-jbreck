int lg_n_helper(int n) {
    int i;
    int r = 0;
    int j;
    //__VERIFIER_assume(n > 0);
    __VERIFIER_assume(n > 0);
    for(i = 1; i != n; i *= 2) {
        r ++;
    }
    return r;
}

int n_lg_n_helper(int n) {
    int i;
    int r = 0;
    for(i = 0; i != n; i++) {
        r += lg_n_helper(n);
    }
    return r;
}
int recursive(int n) {
    //__VERIFIER_assume(n >= 2);
    if (n == 2) { return 2; }
    return recursive(n/2) + recursive(n/2) + n;
}
void main(int n) {
    //__VERIFIER_assume(n > 2);
    int final = recursive(n);
    int bound = lg_n_helper(n);
    if (__VERIFIER_nondet_int()) {
        __VERIFIER_assert(final <= bound);
    }
}

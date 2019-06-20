int lg_n_helper(int n) {
    int i;
    int r = 0;
    int j;
    __VERIFIER_assume(n > 0);
    for(i = 1; i != n; i *= 2) {
        r ++;
    }
    return r;
}
int pow2_helper(int n) {
    int p = 1;
    for(int i = 0; i != n; i++) {
        p *= 2;
    }
    return p;
}
int __cost;
int recursive(int n) {
    __VERIFIER_assume(n >= 2);
    if (n >= 2 && n <= 4) { __cost += 4; return 0; }
    int m = n/2;
    int retval = 0;
    recursive(m);
    retval = recursive(n-m); 
    __cost += n;
    return retval + 1;
}
void main(int n) {
    __cost = 0;
    __VERIFIER_assume(n > 4);
    int final = recursive(n);
    //int height = lg_n_helper(n)-1; // Yes
    //int bound = height;
    //if (__VERIFIER_nondet_int()) {
    //    __VERIFIER_assert(final <= bound);
    //}
    //__cost = final;
    int height = lg_n_helper(n)-1; 
    int bound = 4*pow2_helper(height)+4*pow2_helper(height)*height;
    __VERIFIER_assume(height >= 0);
    __VERIFIER_assume(bound >= 0);
    if (__VERIFIER_nondet_int()) {
        __VERIFIER_assert(__cost <= bound);
    }
}

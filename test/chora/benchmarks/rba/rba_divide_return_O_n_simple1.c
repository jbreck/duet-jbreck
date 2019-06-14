int __cost;
int recursive(int n) {
    __VERIFIER_assume(n >= 2);
    if (n == 2) { return 1; }
    return recursive(n/2) + recursive(n/2);
}
void main(int n) {
    __VERIFIER_assume(n > 2);
    __cost = recursive(n);
    //int bound = 2*n+1;
    //if (__VERIFIER_nondet_int()) {
    //    __VERIFIER_assert(__cost <= bound);
    //}
}

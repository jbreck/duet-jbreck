int __cost;
void recursive(int n) {
    // This version of the benchmark has no assume in this procedure
    __cost++;
    if (n == 0 || n == -1) return;
    int step = (__VERIFIER_nondet_int()) ? 1 : 2;
    recursive(n-step);
}
void main(int n) {
    __VERIFIER_assume(n >= 2);
    recursive(n);
}

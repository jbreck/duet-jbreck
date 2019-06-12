int __cost;
void recursive(int n) {
    __VERIFIER_assume(n >= 0);
    __cost++;
    if (n <= 0) return;
    int step = (__VERIFIER_nondet_int()) ? 1 : 2;
    recursive(n-step);
}
void main(int n) {
    __VERIFIER_assume(n >= 1);
    recursive(n);
}

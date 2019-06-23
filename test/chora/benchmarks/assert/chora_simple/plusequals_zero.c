int __cost;
int pow2_helper(int n) {
    int i;
    int r = 1;
    __VERIFIER_assume(n >= 0);
    for(i = 0; i != n; i++) {
        r = r * 2;
    }
    return r;
}
void recursive(int n) {
    if (n == 1) { /*__cost += 0;*/ return; }
    recursive(n-1);
    recursive(n-1);
    __cost ++;
}
void main(int n) {
    __cost = 0;
    recursive(n);
    int bound = pow2_helper(n-1);
    __VERIFIER_assert(__cost <= bound);
}

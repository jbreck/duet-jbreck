int __cost;
//int lg_n_helper(int n) {
//    int i;
//    int r = 0;
//    int j;
//    //__VERIFIER_assume(n > 0);
//    for(i = 1; i != n; i *= 2) {
//        r ++;
//    }
//    return r;
//}
int recursive(int n) {
    __VERIFIER_assume(n >= 2);
    if (n == 2) { return 0; }
    recursive(n/2);
    return recursive(n/2) + 1;
}
void main(int n) {
    __VERIFIER_assume(n > 2);
    __cost = recursive(n);
    //int bound = lg_n_helper(n);
    //if (__VERIFIER_nondet_int()) {
    //    __VERIFIER_assert(__cost <= bound);
    //}
}

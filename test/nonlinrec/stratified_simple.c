int __cost;
int recursive(int n) {
    if (n == 1) { __cost += 0; return 1; }
    int retval = recursive(n-1) + recursive(n-1);
    // __cost stratifies above retval
    __VERIFIER_assume(retval >= 0);
    __cost += retval;
    return retval;
}
void main(int n) {
    recursive(n);
}

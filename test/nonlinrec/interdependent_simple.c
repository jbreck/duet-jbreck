int __cost;
int recursive(int n) {
    if (n == 1) { __cost += 0; return 1; }
    int retval = recursive(n-1) + recursive(n-1);
    // __cost and retval are interdependent
    __VERIFIER_assume(retval >= 0);
    __cost += retval;
    retval += __cost;
    return retval;
}
void main(int n) {
    recursive(n);
}

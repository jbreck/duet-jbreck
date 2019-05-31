int __cost;
int g;
int recursive(int n) {
    if (n == 1) { __cost += 0; return 1; }
    int retval = recursive(n-1) + recursive(n-1);
    // __cost cannot be proved to be related to g
    //__VERIFIER_assume(g >= 0); // we would need this assumption
    __cost += g;
    return retval;
}
void main(int n) {
    recursive(n);
}

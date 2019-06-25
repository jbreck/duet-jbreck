int __cost;
int recursive(int n) {
    __VERIFIER_assume(n >= 4);
    if (n == 4) { return 0; }
    recursive(n/2);
    return recursive(n/2) + 1;
}
void main(int n) {
    __VERIFIER_assume(n > 4);
    __cost = recursive(n);
}

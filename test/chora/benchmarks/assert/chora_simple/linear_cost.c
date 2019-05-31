int __cost;
void linear(int n) {
    if (n == 1) { __cost++; return; }
    int temp_cost = __cost;
    linear(n-1); // Cost of this call is ignored
    __cost = temp_cost;
    __cost++;
    linear(n-1);
}
void main(int n) {
    __cost = 0;
    linear(n);
    __VERIFIER_assert(__cost <= n);
}

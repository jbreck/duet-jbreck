int __cost;
void recursive(int n) {
    if (n <= 1) { __cost++; return; }
    int temp_cost = __cost;
    recursive(n/2); // Cost of this call is ignored
    __cost = temp_cost;
    __cost++;
    recursive(n/2);
}
void main(int n) {
    recursive(n);
}

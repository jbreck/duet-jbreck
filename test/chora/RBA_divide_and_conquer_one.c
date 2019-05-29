int __cost;
void recursive(int n) {
    if (n <= 1) { __cost++; return; }
    recursive(n/2);
    recursive(n/2);
    __cost += 1;
}
void main(int n) {
    recursive(n);
}

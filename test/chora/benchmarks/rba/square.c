int __cost;
void square(int n) {
    if (n <= 1) { __cost++; return; }
    square(n-1);
    square(n-1);
    __cost += n * n;
}
void main(int n) {
    square(n);
}

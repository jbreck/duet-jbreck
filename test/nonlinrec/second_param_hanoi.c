int __cost;
void hanoi(int m, int n) {
    if (n == 1) { __cost++; return; }
    hanoi(m,n-1);
    __cost++;
    hanoi(m,n-1);
}
void main(int n) {
    hanoi(4,n);
}

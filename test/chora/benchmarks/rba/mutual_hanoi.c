int __cost;
void hanoi1(int n) {
    if (n == 1) { __cost++; return; }
    hanoi2(n-1);
    __cost++;
    hanoi2(n-1);
}
void hanoi2(int n) {
    if (n == 1) { __cost++; return; }
    hanoi1(n-1);
    __cost++;
    hanoi1(n-1);
}
void main(int n) {
    hanoi1(n);
}

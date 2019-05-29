int __cost;
void hanoi(int n) {
    if (n == 1) { return; }
    hanoi(n-1);
    __cost++; 
    hanoi(n-1);
}
void main(int n) {
    hanoi(n);
}

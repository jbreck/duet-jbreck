int __cost;
void recursive(int n) {
    __cost+=n*n*n*n;
    if (n <= 1) {return;}
    recursive(n/2);
}
void main(int n) {
    recursive(n);
}

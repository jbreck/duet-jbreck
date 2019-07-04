int __cost;

void loop (int n) {
    if (n==0) return;
    __cost++;
    loop(n-1);
}

void recursive(int n) {
    loop(n);
    if (n <= 1) {return;}
    recursive(n/2);
}
void main(int n) {
    recursive(n);
}

int __cost;
void hanoi(int n) {
    if (n == 1) { __cost++; return; }
    hanoi(n-1);
    __cost++;
    hanoi(n-1);
}
//void p(int n) {
//    hanoi(n);
//}
//void q(int n) {
//    hanoi(n);
//    hanoi(n);
//}
//void r(int n) {
//    hanoi(n-1);
//    hanoi(n-1);
//}
//void s(int n) {
//    hanoi(n-1);
//    __cost++;
//    hanoi(n-1);
//}
void t(int n) {
    if (n == 1) { __cost++; return; }
    hanoi(n-1);
    __cost++;
    hanoi(n-1);
}
void main(int n) {
    hanoi(n);
    //p(n);
    //q(n);
    //r(n);
    //s(n);
    t(n);
}

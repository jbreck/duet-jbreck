int __cost;
void main(int n) {
  int m = 1;
  __cost = 0;
  __VERIFIER_assume(n > 4);
  while(n != 4) {
    __VERIFIER_assume(n > 4);
    n = n / 2;
    __cost++;
    m = 3 * m;
  }
  __cost = m;
}

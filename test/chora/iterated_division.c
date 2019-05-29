int __cost;
void main(int n) {
  __cost = 0;
  //__VERIFIER_assume(n >= 2);
  while(n != 1) {
    n = n / 2;
    __cost++;
  }
}

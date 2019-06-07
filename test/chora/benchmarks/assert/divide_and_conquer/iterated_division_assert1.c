int __cost;

int lg_n_helper(int n) {
    int i;
    int r = 0;
    int j;
    __VERIFIER_assume(n > 0);
    for(i = 1; i != n; i *= 2) {
        r ++;
    }
    return r;
}

void main(int n) {
  __cost = 0;
  __VERIFIER_assume(n > 2);
  while(n != 2) {
    __VERIFIER_assume(n > 2);
    n = n / 2;
    __cost++;
  }
  if (__VERIFIER_nondet_int()) {
    int bound = lg_n_helper(n+1);
    __VERIFIER_assert(__cost <= bound);
  }
}

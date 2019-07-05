int cost = 0;

int lg_n_helper(int n) {
  int r = 0;
  for(int i = 1; i < n; i *= 2) {
    r ++;
  }
  return r;
}

void recursive(int n) {
  //__VERIFIER_assume(n >= 0);
  if (n == 2 || n == 3) {
    cost += 4;
    return;
  }
  int m = n/2;
  recursive(m);
  recursive(m);
  cost += n;
  return;
}

void main(int n) {
  recursive(n);
  int height = lg_n_helper(n);
  __VERIFIER_assert(cost < 4*(n + n*height));
}

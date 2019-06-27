int cost = 0;

int lg_n_helper(int n) {
  int r = 0;
  for(int i = 1; i < n; i *= 2) {
    r ++;
  }
  return r;
}

void recursive(int n) {
  if (n == 2 || n == 3 || n == 4) {
    cost += 4;
    return 0;
  }
  int m = n/2;
  recursive(m);
  recursive(n-m);
  cost += n;
  return;
}
void main(int n) {
  __VERIFIER_assume(n >= 4);
  recursive(n);
  int height = lg_n_helper(n);
  __VERIFIER_assert(cost < 4*(n + n*height));
}

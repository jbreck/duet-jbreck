int cost = 0;

void recursive(int n) {
  __VERIFIER_assume(n >= 0);
  if (n == 3 || n == 4 || n == 5) {
    cost += 5;
    return;
  }
  int m = n/3;
  recursive(m);
  recursive(m);
  recursive(m);
  cost += n;
  return;
}

void main(int n) {
  recursive(n);
}

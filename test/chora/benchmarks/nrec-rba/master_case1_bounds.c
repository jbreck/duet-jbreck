//case1/a-two/b-four/add-const/a_two_b_four_add_const.c
// Answer: O(sqrt(n))  i.e.  2^log_4(N)
int __cost = 0;

void recursive(int n) {
  if (n == 4 || n == 5 || n == 6 || n == 7) {
    __cost++;
    return;
  }
  int m = n/4;
  recursive(m);
  recursive(m);
  __cost++;
  return;
}

void main(int n) {
  recursive(n);
}

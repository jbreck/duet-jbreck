// case2/a-four/b-two/add-quad/a_four_b_two_add_quad_loop.c
// Answer: O(n^2*lg(n))
int __cost = 0;

void loop (int n) {
    int i,j;
    for (i=0; i<n; i++){
        for(j=0;j<n; j++){
            __cost++;
        }
    }
}

void recursive(int n) {
  if (n == 2 || n == 3) {
    __cost += 3;
    return;
  }
  int m = n/2;
  recursive(m);
  recursive(m);
  recursive(m);
  recursive(m);
  loop(m);
  return;
}

void main(int n) {
  recursive(n);
}

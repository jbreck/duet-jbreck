void f(int d) {
  int x, y, k, z = 1;
  L1:
  while (z < k) { z = 2 * z; }
  assert(z>=2);
  L2:
  while (x > 0 && y > 0) {
     int c = rand();
    if (c) {
      P1:
      x = x - d;
      y = rand();
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

void main() {
    int c = rand();
    if (c) {
	f(1);
    } else {
	f(2);
    }
}



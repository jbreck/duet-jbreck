int __cost;

void matMult (int n, int ax, int ay, int bx, int by){
  __VERIFIER_assume(n >= 2);
  if (n == 2 || n == 3) { return; }
  //if (n <= 3) { return; }
  //int m = n - (n/2);
  int z = n;
  int m = n / 2;
  __VERIFIER_assume(n <= m * 2 + 1);
  //__VERIFIER_assert(n <= m * 2 + 1);
  //__VERIFIER_assume(m >= 0);
  int mpax = m + ax;
  int mpay = m + ay;
  int mpbx = m + bx;
  int mpby = m + by;
  matMult(m,   ax,   ay,   bx,   by);
  matMult(m, mpax,   ay,   bx,   by);
  matMult(m,   ax, mpay, mpbx,   by);
  matMult(m, mpax, mpay, mpbx,   by);
  matMult(m,   ax,   ay,   bx, mpby);
  matMult(m, mpax,   ay,   bx, mpby);
  matMult(m,   ax, mpay, mpbx, mpby);
  //matMult(m, mpax, mpay, mpbx, mpby);
  //
  //for (int i = 0; i < n * n; i++) {
  //int k = __VERIFIER_nondet_int(); 
  //__VERIFIER_assume(k <= (m * 2 + 1) * (m * 2 + 1));
  //__VERIFIER_assume(k >= 0);
  //int k = (m - 3) * (m - 3) * 4;
  //for (int i = 0; i < k; i++) {
  //  __cost++;
  //}

  //int k = (m - 3) * (m - 3);
  //__VERIFIER_assume(k >= 0);
  //__cost += k;

  //__cost += m;
  //__cost += n;   // can handle   (but isn't correct)
  //__cost += n*n; // can't handle (and is correct)
  __cost += 18*m*m;
  //for(int i = 0; i < 18; i++) {
  //    for(int j = 0; j < m; j++) {
  //        for(int k = 0; k < m; k++) {
  //            __cost ++;
  //        }
  //    }
  //}
  //__cost += z * z;
}

void main (int N){
  matMult(N, 0, 0, 0, 0);
}

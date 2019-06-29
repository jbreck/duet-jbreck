int __cost;

// TODO-J: Ideally we'd turn this into Strassen's algorithm if we can,
//   just because that has a more impressive-looking bound

void matMult (int n, int ax, int ay, int bx, int by){
  // TODO-J: I might be able to remove this assumption by re-purposing the
  //   depth-bound analysis as something that gets an invariant about what
  //   input values can ever reach the base case.  Or, we could replace this
  //   assumption in other ways.
  __VERIFIER_assume(n >= 2);

  // TOOD-J: fill in base case with 2x2/3x3 multiplication 
  if (n == 2 || n == 3) { return; }

  // TODO-J: Handle n by m matrices that such that:
  //  (i)   n != m
  //  (ii)  n is not necessarily 2^k for some k (likewise for m)
  int m = n / 2;

  // TODO-Z: (SECONDARY PROBLEM) Remove the need for the assumption below.
  //   I would have thought we would have realized that the below
  //   assumption holds because m = n / 2; but, we don't seem to.
  __VERIFIER_assume(n <= m * 2 + 1);

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
  matMult(m, mpax, mpay, mpbx, mpby); 
  // Note: you can comment out one of the above multiplications to
  //   (*very* roughly) simulate what our analyzer would get on Strassen's
  //   algorithm or something like that.  Note that, for Strassen's algorithm,
  //   the constant 4 in the additive term below will also change to be
  //   something else.  But, we'll fix that later.


  // -- ADDITIVE TERM

  // Note:
  //   One question here is why we can handle (**) but not (*).  This is
  //   an optional, low-priority issue because we actually want to do something
  //   like what's shown in under "PRIMARY PROBLEM" below.  I'm guessing that
  //   the reason we can't handle (*) is related to the reason we couldn't
  //   handle the example that Antonio sent us a few months ago, so I was
  //   thinking that Generalized Fourier-Motzkin might help us here.

  // Two options for a model additive term, which I call (**) and (*):

  //__cost += n*n;  // can't handle (and is correct) (*)

  __cost += 4*m*m;  // can handle (**). goal: replace this with the code below

  // The preferred alternative, which is a more realistic additive term:

  // TODO-Z: (PRIMARY PROBLEM) I really wish we could handle something like this
  //   rather than the above line that's marked with a (**)
  //for(int i = 0; i < 4; i++) {
  //    for(int j = 0; j < m; j++) {
  //        for(int k = 0; k < m; k++) {
  //            __cost ++;
  //        }
  //    }
  //}
}

void main (int N){
  matMult(N, 0, 0, 0, 0);
}

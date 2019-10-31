int __cost = 0;

int binary_search(int *aArray, int aX, int pBegin, int pn) {
  __VERIFIER_assume(pn>0);
  __cost++;
  if (pn < 2) {
    return aArray[pBegin];
  } else {
    pn = pn / 2;
    if (aX < aArray[pBegin]) {
      return binary_search(aArray, aX, pBegin, pn);
    } else {
      int pMid = pBegin + pn;
      return binary_search(aArray, aX, pMid, pn);
    }
  }
}

int main(int N) {
  int *aArray = (int*)malloc(N*sizeof(int));
  int x = __VERIFIER_nondet_int();
  binary_search(aArray, x, 0, N);
}

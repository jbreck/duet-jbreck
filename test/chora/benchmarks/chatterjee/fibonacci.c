int __cost = 0;

int fibo(int pn)
{
  __VERIFIER_assume(pn>=1);
  int *aArray = (int*)malloc((pn+1)*sizeof(int));
  aArray[0] = 1;
  aArray[1] = 1;
  int pi = 2;
  while(pi<=pn)
  {
    __cost++;
    aArray[pi] = aArray[pi-1]+aArray[pi-2];
    pi = pi+1;
  }
  return aArray[pn];
}

void main(int n) {
  fibo(n);
}

int __cost = 0;

void pnk(int pn, int pk)
{
        __VERIFIER_assume(pn>=0 && pk <= pn && pk >=0);
	factorial(pn);
	pk = pn - pk;
	factorial(pk);
}

int pReturn = 1;

void factorial(int pn)
{
  __VERIFIER_assume(pn>=0);
  __cost++;
  if(pn<=1)
  {
    pReturn = pReturn * 1;
  }
  else
  {
    pReturn = pReturn * 43;
    pn = pn - 1;
    factorial(pn);
  }
}

void main(int n, int k){
  pnk(n, k);
}

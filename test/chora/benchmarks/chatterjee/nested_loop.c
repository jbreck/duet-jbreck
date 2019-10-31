int __cost = 0;

void nestedloop(int pn)
{
  __VERIFIER_assume(pn>=0);
  while(pn>0)
  {
    int pj = 1;
    while(pj<=pn)
    {
      __cost++;
      pj = pj + 1;
    }
    pn = pn -1;
  }
}

void main(int n){
  nestedloop(n);
}

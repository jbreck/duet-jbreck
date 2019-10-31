int __cost = 0;

void loop(int pi, int pj, int pm, int pn)
{
  __VERIFIER_assume(pi<=pm+1 && pj<=pn+1 && pi>=0 && pj>=0 && pm>=0 && pn>=0);
  __cost++;
  if(pi<=pm)
  {
    if(pj<=pn)
    {
      pj = pj + 1;
    }
    else
    {
      pi = pi + 1;
      pj = 0;
    }
    loop(pi, pj, pm, pn);
  }
}

void main(int i, int j, int m, int n){
  loop(i, j, m, n);
}

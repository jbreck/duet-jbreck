void foo()
{
  int y=0;
  _Bool c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();
  if (c1) y++;
  if (c2) y--;
  else y+=10;
}

int main()
{
  int d = 1;
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x <= 1000000 && x >= -1000000);
  _Bool c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();

  if (c1) d = d - 1;
  if (c2) foo();

  c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();

  if (c1) foo();
  if (c2) d = d - 1;
  
  while(x>0)
  {
    x=x-d;
  }

  __VERIFIER_assert(x<=0);
}

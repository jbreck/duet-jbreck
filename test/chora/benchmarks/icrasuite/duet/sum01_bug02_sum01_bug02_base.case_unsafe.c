#define a (2)

void main() { 
    int i, n=rand(), sn=0;
    assume(n >= 0);
  for(i=1; i<=n; i++) {
    sn = sn + a;
    if (i==4) sn=-10;
  }
  assert(sn==n*a || sn == 0);
}

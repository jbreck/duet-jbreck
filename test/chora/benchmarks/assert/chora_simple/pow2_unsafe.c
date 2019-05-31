#include "pow.h"

DECLARE_POW(2); // This defines a function called icra_pow2.

int __cost;

void doubler(int n) {
   if (n == 1) {__cost++; return;}
   doubler(n-1);
   doubler(n-2);
}

void main(int n) {
   __cost = 0;
   doubler(n);
   int p = icra_pow2(n-3);
   __VERIFIER_assert(__cost <= p);
}

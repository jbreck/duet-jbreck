int four(int n) {
   if (n <= 1) { 
      int r = __VERIFIER_nondet_int();
      __VERIFIER_assume(r <= 1);
      return r; 
   }
   int total = 0;
   for(int i = 0; i < 4; i++) {
      total += four(n-1);
   }
   return total;
}

int main(int n) {
   return four(n);
}

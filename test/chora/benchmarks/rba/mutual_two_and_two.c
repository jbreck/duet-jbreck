int __cost;
void two_a(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 2; i++) {
      two_b(n-1);
   }
}
void two_b(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 2; i++) {
      two_a(n-1);
   }
}
void main(int n) {
   two_a(n);
}

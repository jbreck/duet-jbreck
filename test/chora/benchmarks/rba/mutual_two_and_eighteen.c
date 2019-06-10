int __cost;
void eighteen(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 18; i++) {
      two(n-1);
   }
}
void two(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 2; i++) {
      eighteen(n-1);
   }
}
void main(int n) {
   eighteen(n);
}

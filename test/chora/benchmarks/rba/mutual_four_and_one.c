int __cost;
void four(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 4; i++) {
      one(n-1);
   }
}
void one(int n) {
   if (n <= 1) { __cost++; return; }
   for(int i = 0; i < 1; i++) {
      four(n-1);
   }
}
void main(int n) {
   four(n);
}

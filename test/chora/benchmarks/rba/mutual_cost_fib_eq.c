int __cost;

void fib1(int n) {
   if (n == 1) {__cost++; return;}
   fib2(n-1);
   fib2(n-2);
}

void fib2(int n) {
   if (n == 1) {__cost++; return;}
   fib1(n-1);
   fib1(n-2);
}

void main(int n) {
   fib1(n);
}

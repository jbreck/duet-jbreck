int __cost;

void fib(int n) {
   if (n == 1) {__cost++; return;}
   fib(n-1);
   fib(n-2);
}

void main(int n) {
   fib(n);
}

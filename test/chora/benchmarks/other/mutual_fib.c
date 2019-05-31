int fib_a(int n) {
   if (n <= 1) return 1;
   return fib_b(n-1) + fib_b(n-2);
}

int fib_b(int n) {
   if (n <= 1) return 1;
   return fib_a(n-1) + fib_a(n-2);
}

int main(int n) {
   return fib_a(n);
}

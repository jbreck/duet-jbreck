#include "tick.h"
void eighteen(int n) {
   if (n <= 1) { tick(1); return; }
   for(int i = 0; i < 18; i++) {
      two(n-1);
   }
}
void two(int n) {
   if (n <= 1) { tick(1); return; }
   for(int i = 0; i < 2; i++) {
      eighteen(n-1);
   }
}
void main(int n) {
   init_tick(0);
   eighteen(n);
}

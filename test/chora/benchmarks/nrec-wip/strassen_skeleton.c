#include "tick.h"

void strassen(int * matrix, int ax, int ay, int bx, int by, int len) {
  __VERIFIER_assume(len >= 0);
  int cutoff_len = 3;
  if (len <= cutoff_len) {
    __cost += cutoff_len*cutoff_len*cutoff_len;
    return;
  }
  int half_len = len/2;
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  strassen(matrix,ax,ay,bx,by,half_len);
  for(int i = 0; i < half_len; i++) {
    for(int j = 0; j < half_len; j++) {
      __cost++;
    }
  }
  return;
}

void main(int * matrix, int len) {
  init_tick(0);
  __VERIFIER_assume(len >= 0);
  strassen(matrix,0,0,0,0,len);
}

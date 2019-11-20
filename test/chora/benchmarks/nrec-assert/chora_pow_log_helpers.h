int pow2_helper(int n) {
    int r = 1;
    for(int i = 0; i != n; i++) {
        r = 2*r;
    }
    return r;
}

int log2_helper(int n) {
  int r = 0;
  for(int i = 1; i < n; i *= 2) {
    r ++;
  }
  return r;
}                                 

#define DEFINE_POW(BASE)                 \
    int pow ## BASE ## _helper (int n) { \
        int r = 1;                       \
        for(int i = 0; i != n; i++) {    \
            r = BASE * r;                \
        }                                \
        return r;                        \
    }

#define DEFINE_LOG(BASE)                 \
    int log ## BASE ## _helper (int n) { \
        int r = 0;                       \
        for(int i = 1; i < n; i *= 2) {  \
          r ++;                          \
        }                                \
        return r;                        \
    }                                


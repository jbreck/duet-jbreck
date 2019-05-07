int __cost;
int recursive(int hi, int lo) {
    if (hi-lo == 1) { __cost += 0; return 1; }
    int retval = recursive(hi-1,lo) + recursive(hi,lo+1);
    // __cost stratifies above (hi-lo)
    __cost += hi-lo;
    return retval;
}
void main(int n) {
    recursive(n,0);
}

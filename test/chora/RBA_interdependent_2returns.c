int __cost;
int return1;
int return2;
void recursive(int n) {
    if (n == 1) { return1 = 1; return2 = 1; return; }
    recursive(n-1);
    int temp_return1_a = return1;
    int temp_return2_a = return2;
    recursive(n-1);
    int temp_return1_b = return1;
    int temp_return2_b = return2;
    return2 = temp_return1_a + temp_return1_b;
    return1 = temp_return2_a + temp_return2_b;
    return;
}
void main(int n) {
    return1 = 1;
    return2 = 1;
    __VERIFIER_assume(n >= 0);
    recursive(n);
    __cost = return1;
}

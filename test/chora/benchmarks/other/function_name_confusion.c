int __cost;
int i_am_a_global;

void never_addressed_function(int n) { }
void my_address_gets_taken(int n) { }
void name_used_both_ways(int n) { } // note: weird
int  i_get_called(int n) { return n+1;} 
int  i_am_declared_but_not_defined(int n);

void hanoi(int n) {
    int i_am_a_local = 1;
    int name_used_both_ways = 5; // note: weird
    int nd = __VERIFIER_nondet_int(); 
    int temp2 = i_get_called(n);
    int temp3 = i_get_called_but_i_am_not_declared(n);
    int temp4 = i_am_declared_but_not_defined(n);
    __VERIFIER_assume(i_am_a_local >= 0);
    __VERIFIER_assum(i_am_a_local >= 0);
    if (n == 1) { __cost++; return; }
    hanoi(n-1);
    __cost++;
    hanoi(n-1);
}
void main(int n) {
    never_addressed_function(1);
    void * temp = &my_address_gets_taken;
    hanoi(n);
}

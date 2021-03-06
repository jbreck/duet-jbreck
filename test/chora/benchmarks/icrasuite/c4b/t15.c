#include "assert.h"

// C4B output: |[0,x]|

#include "tick.h"

void start(int x, int y)
{
	int z;

	__VERIFIER_assume(y >= 0);
	while (x > y) {
		tick(1);
		x -= y + 1;
		for (z = y; z > 0; z--) {
		    tick(1);
		}
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = (x > 0) ? x : 0;
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

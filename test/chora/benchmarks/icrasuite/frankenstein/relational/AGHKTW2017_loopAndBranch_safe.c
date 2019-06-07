/* Source: Timos Antonopoulos, Paul Gazzillo, Michael Hicks, Eric Koskinen,
   Tachio Terauchi, Shiyi Wei: Decomposition Instead of Self-Composition for
   Proving the Absence of Timing Channels.  PLDI 2017 */

/* Modified version of a program in the above paper. This one is for sure safe */

#include "assert.h"

int loopAndbranch_safe(int high, int low) {
    int i = low;
    int tick = 0;
    if (low < 0) {
	while (i > 0) {
	    tick++;
	    i--;
	}
    } else {
	low = low + 10; // low is above 0
	if (low >= 10) {
	    int j = low;
	    while (j > 0) {
		j--;
		tick++;
	    }
	} else {
	    if (high < 0) { //this branch would reveal info, but it is infeasible
		int k = low;
		while (k>0) {
		    k--;
		    tick++;
		}
	    }
	}
    }
    return tick; //tick is solely some function of low
}

void main() {
    int high1 = __VERIFIER_nondet_int();
    int high2 = __VERIFIER_nondet_int();
    int low = __VERIFIER_nondet_int();
    __VERIFIER_assert(loopAndbranch_safe(high1,low) == loopAndbranch_safe(high2,low));
}

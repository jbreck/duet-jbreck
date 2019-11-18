// Adapted from: https://costa.fdi.ucm.es/pubs/examples.php
/*

% EQUATIONS
%
eq(p(X),1,[],[X=0]).
eq(q(X),1,[],[X=0]).
eq(p(X),1,[p(X-1),q(X-1)],[X>=0]).
eq(q(X),1,[q(X-1),p(X-1)],[X>=0]).

*/

#include "tick.h"

void p(int X) {
    __VERIFIER_assume(X >= 0);
    if (X >= 1) {
        tick(1);
        p(X-1);
        q(X-1);
    }
}

void q(int X) {
    __VERIFIER_assume(X >= 0);
    if (X >= 1) {
        tick(1);
        q(X-1);
        p(X-1);
    }
}

void main(int X) {
    init_tick(0);

    p(X);
}

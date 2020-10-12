from nagini_contracts.contracts import (
    Acc,
    Assert,
    Invariant,
    Implies,
    Predicate,
    Requires,
    Ensures,
    Result,
)
from nagini_contracts.obligations import *
from nagini_contracts.lock import Lock

class ObjectLock(Lock[object]):
    @Predicate
    def invariant(self) -> bool:
        return True

"""
method adjusted from tests\obligations\verification\test_waitlevels.py 
soundness condition does not hold: 
In the final iteration of the loop the acquired lock is not released. Hence in 
the inlined program after the loop, there is still an obligation left and the 
leak check fails. However, in the Viper encoding it is possible to write an invariant
which makes sure that the final obligation is leaked.
In the Python program writing such an invariant would lead to an error (since 
a leak check occurs at the end of the modular loop check). Reflecting this 
in the inlined Viper program requires more information than what standard
inlining does.
"""
def locks_creating_loop_error(n: int) -> ObjectLock:
    Requires(n > 0)
    l = ObjectLock(object())
    i = 0
    while i < n:
        Invariant(l is not None)
        Invariant(WaitLevel() < Level(l))
        l.acquire()
        #don't release
        if (i+2 < n):
            l.release()
        l = ObjectLock(object())
        i += 1
    return l
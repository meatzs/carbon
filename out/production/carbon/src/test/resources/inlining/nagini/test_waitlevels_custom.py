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
  method inspired by from tests\obligations\verification\test_waitlevels.py
"""
#:: ExpectedOutput(carbon)(leak_check.failed:method_body.leaks_obligations)
def create_lock_unknown_order_2() -> None:
    someLock = ObjectLock(object())
    someLock.acquire()
    release_lock(someLock)
    l1 = ObjectLock(object())
    l2 = ObjectLock(object())
    l2.acquire()
    #:: ExpectedOutput(call.precondition:assertion.false)
    l1.acquire()
    l1.release()
    l2.release()

def release_lock(l: ObjectLock) -> None:
    Requires(MustRelease(l))
    l.release()

"""
  fundamental errors: 
  Second lock (l1) cannot be acquired (wait level of l1 is
  not known to be larger than that of l2)

  Note that since no obligations are leaked in the inlined program, the leak check
  at the end is not an issue.
"""
def create_lock_unknown_order_2_client() -> None:
    create_lock_unknown_order_2()

"""
method inspired by tests\obligations\verification\test_waitlevels.py 
(made n a parameter instead of a fixed value)
"""
# method inspired from tests\obligations\verification\test_waitlevels.py
def create_lock_below_2(n: int) -> None:
    l1 = ObjectLock(object())
    l2 = ObjectLock(object(), below=l1)
    i = 0

    while i < n :
        Invariant(WaitLevel() < Level(l2))
        Invariant(Level(l2) < Level(l1))

        l2.acquire()
        l1.acquire()
        l1.release()
        l2.release()
        l1 = ObjectLock(object())
        l2 = ObjectLock(object(), below=l1)
        i += 1

"""
method adjusted from tests\obligations\verification\test_waitlevels.py 
soundness condition holds, no fundamental errors for any inlining bound
"""
def locks_creating_loop(n: int) -> ObjectLock:
    Ensures(WaitLevel() < Level(Result()))
    l = ObjectLock(object())
    i = 0
    while i < n:
        Invariant(l is not None)
        Invariant(WaitLevel() < Level(l))
        l.acquire()
        l.release()
        l = ObjectLock(object())
        i += 1
    return l

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
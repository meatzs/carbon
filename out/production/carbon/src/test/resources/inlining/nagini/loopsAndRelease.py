# Any copyright is dedicated to the Public Domain.
# http://creativecommons.org/publicdomain/zero/1.0/

"""
This test is a ported version of
``obligations/loopsAndRelease.chalice`` test from Chalice2Silver test
suite.
"""


from nagini_contracts.contracts import (
    Assert,
    Invariant,
    Predicate,
    Requires,
)
from nagini_contracts.obligations import *
from nagini_contracts.lock import Lock


class ObjectLock(Lock[object]):
    @Predicate
    def invariant(self) -> bool:
        return True

#:: ExpectedOutput(leak_check.failed:method_body.leaks_obligations)
def f_leak(a: ObjectLock) -> None:
    Requires(a is not None)
    Requires(WaitLevel() < Level(a))

    a.acquire()
    i = 0
    n = 10
    while i < n:
        i += 1
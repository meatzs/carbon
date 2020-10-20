# Any copyright is dedicated to the Public Domain.
# http://creativecommons.org/publicdomain/zero/1.0/

from nagini_contracts.contracts import *


class A:
    def __init__(self) -> None:
        self.a = 12
        Ensures(Acc(self.a))
        Ensures(MayCreate(self, 'b'))

    def set(self, v: int) -> None:
        Requires(MaySet(self, 'b'))
        self.b = v
        Ensures(Acc(self.b))

    def set2(self, v: int) -> None:
        Requires(MayCreate(self, 'b'))
        self.b = v
        Ensures(Acc(self.b))

    def set3(self, v: int) -> None:
        Requires(MayCreate(self, 'b'))
        self.b = v
        Ensures(MaySet(self, 'b'))

    def set4(self, v: int) -> None:
        Requires(MaySet(self, 'b'))
        self.b = v
        #:: ExpectedOutput(postcondition.violated:assertion.false)
        Ensures(False)

    def set5(self, v: int) -> None:
        Requires(MayCreate(self, 'b'))
        self.b = v
        #:: ExpectedOutput(postcondition.violated:assertion.false)
        Ensures(False)

    def set6(self, v: int) -> None:
        Requires(MayCreate(self, 'b'))
        self.b = v
        #:: ExpectedOutput(postcondition.violated:assertion.false)
        Ensures(False)

    def get(self) -> int:
        Requires(Acc(self.b))
        Ensures(Acc(self.b) and Result() == self.b)
        return self.b


def client_1_1() -> None:
    a = A()
    a.set(56)
    assert a.get() == a.b
    # cannot prove this with the above spec, but there is a spec for which it holds --> no error expected for any inlining bound
    assert a.b == 56


def client_1_2() -> None:
    a = A()
    a.set2(56)
    assert a.get() == a.b
    # cannot prove this with the above spec, but there is a spec for which it holds --> no error expected for any inlining bound
    assert a.b == 56


def client_2() -> None:
    a = A()
    # fundamental error in get(), since a.b has not been created yet
    a.get()


def client_3_1() -> None:
    a = A()
    a.set(56)
    a.set(43)
    assert a.get() == a.b
    # fundamental error, since a.b == 43
    #:: ExpectedOutput(assert.failed:assertion.false)
    assert a.b == 56


def client_3_2() -> None:
    a = A()
    a.set2(56)
    a.set(43)
    # fundamental error since assertion can be reachedb
    #:: ExpectedOutput(assert.failed:assertion.false)
    assert False


def client_3_3() -> None:
    a = A()
    a.set2(56)
    """
    With the above annotation, this call fails when verifying modularly
    however, there is an annotation such that it verifies (Acc(self.b) in both pre- and post for set3). Hence, no error expected for any inlining bound.
    """
    a.set3(43)


def client_4() -> None:
    a = A()
    a.set(56)
    a.b = 12
    assert a.b == 12
    # fundamental error: a.b == 56 does not hold
    #:: ExpectedOutput(assert.failed:assertion.false)
    assert a.b == 56


def client_5() -> None:
    a = A()
    a.set3(23)
    # cannot prove this with the above spec, but there is a spec for which it holds (Acc(self.b) post for set3) --> no error expected for any inlining bound
    b = a.b


def client_6() -> None:
    a = A()
    a.set3(23)
    a.b = 2323
    b = a.b
    assert b == 2323
    # fundamental error since assertion can be reached
    #:: ExpectedOutput(assert.failed:assertion.false)
    assert False


def client_8() -> None:
    a = A()
    a.set3(23)
    # cannot prove this with the above spec, but there is a spec for which it holds (Acc(self.b) post for set3 and Acc(self.b) pre for set2) --> no error expected for any inlining bound
    a.set2(1)
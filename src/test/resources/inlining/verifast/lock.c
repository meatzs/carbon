/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

#include <assert.h>
#include "relaxed.h"
#include "lock.h"

//@ predicate_ctor lock_internal_inv(predicate() Inv)(int value) = value == 1 ? true : Inv() ;

//@ predicate Lock(int *loc, predicate() J) = Write(loc, lock_internal_inv(J)) &*& RMW(loc, lock_internal_inv(J)) ;

void release_lock(int *lock)
    //@ requires Lock(lock, ?J) &*& J();
    //@ ensures Lock(lock, J);
{
    //@ open Lock(lock,J);
    //@ close lock_internal_inv(J)(0);
    atomic_store_explicit(lock,0,memory_order_release);
    //@ close Lock(lock,J);
}

void acquire_lock(int *lock)
    //@ requires Lock(lock, ?J);
    //@ ensures Lock(lock, J) &*& J();
{
    bool b;
    for (;;) 
        //@ invariant Lock(lock, J); 
    { 
        //@ open Lock(_,_);
        /*@ 
            produce_lemma_function_pointer_chunk CAS_premise(0, 1, True, lock_internal_inv(J), J)() { 
                open lock_internal_inv(J)(0); 
                open True(); 
                close lock_internal_inv(J)(1); 
            };
        @*/
        //@ close True();
        b = atomic_compare_exchange_acquire_release(lock, 0, 1);
        if (b) {
            break;
        }
        //@ close Lock (lock, J);
        //@ open True();
    }
    //@ close Lock (lock, J);
}

void new_lock(int *lock)
    //@ requires exists<predicate()>(?J) &*& *lock |-> ?v &*& J();
    //@ ensures Lock(lock, J);
{
    //@ open exists(_);
    *lock = 0;
    //@ close lock_internal_inv(J)(0); 
    //@ convert_to_atomic_rmw(lock, lock_internal_inv(J));
    //@ close Lock(lock, J);
}

/*@

lemma void dup_lock(int *lock)
    requires Lock(lock, ?J);
    ensures Lock(lock, J) &*& Lock(lock, J);
{
    open Lock(lock, J);
    dup_Write(lock);
    dup_RMW(lock);
    close Lock(lock, J);
    close Lock(lock, J);
}

@*/

/* ---------------------------------------
               CLIENT CODE
--------------------------------------- */

//@ predicate A();
//@ predicate B();

void new_lock_A(int *l)
    //@ requires A() &*& exists<predicate()>(A) &*& *l |-> _;
    //@ ensures Lock(l, A);
{
    new_lock(l);
}

void client_1(int *l)
    //@ requires *l |-> _ &*& A();
    //@ ensures Lock(l, A);
{
    new_lock_A(l);
}

void client_1_inlined(int *l)
    //@ requires *l |-> _ &*& A();
    //@ ensures Lock(l, A);
{
    int *lock = l;
    // Since the precondition of new_lock initializes the ghost variable J_1,
    // we have to add this assertion as part of inlining
    //@ assert exists<predicate()>(?J);
    
    //@ open exists(_);
    *lock = 0;
    //@ close lock_internal_inv(J)(0);
    //@ convert_to_atomic_rmw(lock, lock_internal_inv(J));
    //@ close Lock(lock, J);
}

void new_lock_B(int *l)
    //@ requires B() &*& exists<predicate()>(B) &*& *l |-> _;
    //@ ensures Lock(l, B);
{
    new_lock(l);
}

void client_2(int *l1, int *l2)
    //@ requires *l1 |-> _ &*& *l2 |-> _ &*& A() &*& B();
    //@ ensures Lock(l1, A) &*& Lock(l2, B);
{
    //@ close exists<predicate()>(A);
    //@ close exists<predicate()>(B);
    new_lock_A(l1);
    new_lock_B(l2);
}

void client_2_inlined(int *l1, int *l2)
    //@ requires *l1 |-> _ &*& *l2 |-> _ &*& A() &*& B();
    //@ ensures Lock(l1, A) &*& Lock(l2, B);
{
    //@ close exists<predicate()>(A);
    //@ close exists<predicate()>(B);
    
    int *lock_1 = l1;
    // Since the precondition of new_lock initializes the ghost variable J_1,
    // we have to add this assertion as part of inlining
    //@ assert exists<predicate()>(?J_1);
    
    //@ open exists(_);
    *lock_1 = 0;
    //@ close lock_internal_inv(J_1)(0);
    //@ convert_to_atomic_rmw(lock_1, lock_internal_inv(J_1));
    //@ close Lock(lock_1, J_1);
    
    int *lock_2 = l2;
    // Since the precondition of new_lock initializes the ghost variable J_2,
    // we have to add this assertion as part of inlining
    //@ assert exists<predicate()>(?J_2);
    
    //@ open exists(_);
    *lock_2 = 0;
    //@ close lock_internal_inv(J_2)(0);
    //@ convert_to_atomic_rmw(lock_2, lock_internal_inv(J_2));
    //@ close Lock(lock_2, J_2);
}

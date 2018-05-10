#!/usr/bin/env sage
"""Code for Testing Conjectures about Abelian Transducers"""

import itertools
import random

load("binary_invertible_transducer.sage")

def in_edges(T, s):
    r = []
    for k, ((d0, d1), t) in T.data.items():
        if d0 == s or d1 == s:
            r.append((k, t))
    return r

def monogenic(AA):
    T = AA.to_bit()
    F, v = T.field_representation()
    FF = NumberField(reciprocal_poly(F.polynomial()), 'Z')
    OFF = FF.maximal_order()
    Z = FF('Z')
    basis = Z.powers(AA.m)
    if OFF.basis() != basis:
        return AA, OFF.basis()

def num_deltas_eq_num_gaps(AA):
    T = AA.to_bit()
    for Tp in T.terminal_scc_transducers():
        if sum(1 for _ in Tp.gaps()) != sum(1 for _ in Tp.deltas()):
            return Tp.n

conjecture_tests = [
    monogenic,
    num_deltas_eq_num_gaps
]

def test_conjectures_for(AA):
    for test in conjecture_tests:
        result = test(AA)
        if result is not None:
            print "="*80
            print "Counterexample found for " + test.__name__
            print AA
            print repr(AA)
            print "Details:"
            print result
            print "="*80

def test_conjectures(min_dimension=2, max_dimension=4,
                     max_size_for=lambda d: 200*d, iterations=1000):
    """
    Generates matrices and tests all conjectures.

    Prints any counterexamples that appear.
    """
    for _ in range(iterations):
        dimension = randint(min_dimension, max_dimension)
        AA = random_abelian_automaton(dimension, max_size_for(dimension))
        print "Testing", AA
        test_conjectures_for(AA)

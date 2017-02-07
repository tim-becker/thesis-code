#!/usr/bin/env sage
"""Code for Testing Conjectures about Abelian Transducers"""

import itertools
import random

load("binary_invertible_transducer.sage")

def one_terminal_scc(T):
    """
    Checks that the transducer has only one terminal SCC
    """
    B = T.bit()
    l = len(B.terminal_scc_transducers())
    if l != 1: return l

def two_odd_in_implies_even_in(T):
    """
    Checks that in a strongly connected component, if a state has two odd
    parents then it also has its even parent.
    """
    def in_edges(T, s):
        r = []
        for k, ((d0, d1), t) in T.data.items():
            if d0 == s or d1 == s:
                r.append((k, t))
        return r

    B = T.bit()
    for T in B.terminal_scc_transducers():
        for k, ((d0, d1), t) in T.data.items():
            if not t:
                continue
            ed0 = in_edges(T, d0)
            ed1 = in_edges(T, d1)
            if len(ed0) == 2 and ed0[0][1] and ed0[1][1]:
                return d0
            if len(ed1) == 2 and ed1[0][1] and ed1[1][1]:
                return d1

conjecture_tests = [
    one_terminal_scc,
    two_odd_in_implies_even_in
]

def test_conjectures_for(AA):
    for test in conjecture_tests:
        result = test(AA)
        if result is not None:
            print "="*80
            print "Counterexample found for " + test.__name__
            print "\tMatrix:"
            print AA.A
            print "Details:"
            print result
            print "="*80

def test_conjectures(min_dimension=2, max_dimension=4, iterations=1000):
    """
    Generates matrices and tests all conjectures.

    Prints any counterexamples that appear.
    """
    for _ in range(iterations):
        dimension = randint(min_dimension, max_dimension)
        AA = random_abelian_automaton(dimension, 200*dimension)
        print "Testing", AA
        test_conjectures_for(AA)

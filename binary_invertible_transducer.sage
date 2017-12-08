"""
Code implementing Binary Invertible Transducers.

Includes code to compute useful representations of Abelian transducers.
"""
from collections import deque
from copy import copy, deepcopy
import itertools
import operator

load("graph_loop.sage")

# plot settings
PLOT_DPI = 200
PLOT_ITERS = 1000

MAX_DEPTH=10000
sys.setrecursionlimit(MAX_DEPTH)

# Declare 'z'
P.<z> = PolynomialRing(QQ)

# Type of FreeGroupElements; used for assertions
FreeGroupElement = FreeGroup().gens()[0].__class__

def factor(f):
    """
    Compute the factorization of a free group element
    """
    layer = ([x]*c if c > 0 else [x^(-1)]*(-c) for x,c in f.syllables())
    return [x for a in layer for x in a]

def wr(f, A):
    """
    Compute the wreath recursion for the given word `f` in the transducer `A`
    """
    s = factor(f)
    if len(s) == 0:
        I = A.data.keys()[0].parent(1)
        return (I, I), 0
    (d0,d1),t = A.data[s[0]]
    for x in s[1:]:
        (xd0, xd1), xt = A.data[x]
        if t:
            d0 *= xd1
            d1 *= xd0
        else:
            d0 *= xd0
            d1 *= xd1
        t = t ^^ xt
    return (d0, d1), t

class BinaryInvertibleTransducer(object):
    def __init__(self, data, convert=False):
        """
        Construct a BinaryInvertibleTransducer from a dictionary of the form
            { state: ((d0, d1), toggle), ... }
        where d0, d1 are the residuals and toggle is 1 if state is a toggle
        and 0 otherwise

        States are assumed to be elements of a FreeGroup unless convert=True
        """
        self.n = len(data)
        if convert:
            F = FreeGroup(self.n)
            gen = dict(zip(data.keys(), F.gens()))
        newdata = {}
        for k,v in data.items():
            transition, toggle = v
            assert len(transition) == 2, "Incorrect transition length"
            d0,d1 = transition
            assert d0 in data, "{} residual0 {} not present".format(k, d0)
            assert d1 in data, "{} residual1 {}not present".format(k, d1)
            assert toggle == 0 or toggle == 1, "toggle invalid"
            if not convert:
                assert isinstance(k, FreeGroupElement), type(k)
                assert isinstance(d0, FreeGroupElement), type(d0)
                assert isinstance(d1, FreeGroupElement), type(d1)
                newdata[k] = ((d0, d1), toggle)
            else:
                newdata[gen[k]] = ((gen[d0], gen[d1]), toggle)
        self.base_group = newdata.keys()[0].parent()
        self.data = newdata
        self.acc_trans = None
        self.Ai = None

    def states(self):
        return self.data.keys()

    def transduce(self, start, bits):
        """
        Run the transduction from start state on bits.
        Returns end state and output bits
        """
        out = []
        cur = start
        for bit in bits:
            transition, toggle = self.data[cur]
            out.append(toggle ^^ bit) # toggle or copy
            cur = transition[bit]
        return cur, out

    def iterorbit(self, start, x):
        """
        Returns an iterator for the orbit of x under start
        """
        _, y = self.transduce(start, x)
        while y != x:
            yield y
            _, y = self.transduce(start, y)

    def transducer(self):
        """
        Creates a sage built-tin Transducer object for this transducer
        """
        edges = []
        for k, ((d0, d1), t) in self.data.items():
            edges.append((k, d0, 0, t))
            edges.append((k, d1, 1, 1 - t))
        states = self.states()
        return Transducer(edges, initial_states=states, final_states=states)

    def minimized(self):
        """
        Returns a minimized version of `self`. Prefer the state with the
        shortest label from each equivalence class.
        """
        def rep(multistate):
            """
            Returns the representative for the multistate
            Uses the shortest element, breaking ties by lowest index
            """
            multistate = map(lambda v: v.label(), multistate.label())
            minlen = min(map(lambda v: len(v.syllables()), multistate))
            for v in multistate:
                if len(v.syllables()) == minlen:
                    return v

        T = self.transducer().simplification()
        data = {}
        for s in T.states():
            t1, t2 = T.transitions(from_state=s)
            if t2.word_in == 0:
                t1, t2 = t2, t1
            toggle = t1.word_in != t1.word_out
            transition = (rep(t1.to_state), rep(t2.to_state))
            data[rep(s)] = (transition, toggle)
        return BinaryInvertibleTransducer(data)

    def acceptor(self, t):
        """
        Computes the acceptor for a state t
        """
        assert t in self.data
        g = 'g'
        if self.acc_trans is None:
            self.acc_trans = [[g, g, i] for i in [(0,0),(0,1),(1,0),(1,1)]]
            for s, (trans, toggle) in self.data.items():
                self.acc_trans.append([s, trans[0], (0, int(toggle))])
                self.acc_trans.append([s, trans[1], (1, 1-toggle)])
                self.acc_trans.append([s, g, (0, 1-toggle)])
                self.acc_trans.append([s, g, (1, int(toggle))])
        A = Automaton(self.acc_trans, initial_states=[t],
                      final_states=self.states())
        return A.accessible_components()

    def inverse(self):
        if not self.Ai:
            def inv(w):
                ((d0, d1), t) = w
                return ((d1^(-1), d0^(-1)), t) if t else \
                       ((d0^(-1), d1^(-1)), t)
            data = {s^(-1): inv(w) for s, w in self.data.items()}
            self.Ai = BinaryInvertibleTransducer(data)
        return self.Ai

    def product(self, other):
        data = {}
        for s1, (delta1, toggle1) in self.data.items():
            for s2, (delta2, toggle2) in other.data.items():
                d0s1, [b] = self.transduce(s1, [0])
                d0 = d0s1*other.transduce(s2, [b])[0]
                d1s1, [b] = self.transduce(s1, [1])
                d1 = d1s1*other.transduce(s2, [b])[0]
                toggle = toggle1 ^^ toggle2
                data[s1*s2] = ((d0, d1), toggle)
        return BinaryInvertibleTransducer(data)

    def gap(self):
        """
        Return the gap value of an odd state in `self`
        """
        for s, ((d0, d1), toggle) in self.data.items():
            if toggle:
                return d0*d1^(-1)

    def is_free_abelian(self):
        # Free abelian transducers have nontrivial gap value
        if self.minimized().gap().is_one():
            return False
        gap_acc = None
        T = self.minimized()
        AAi = T.product(T.inverse())
        for s, ((d0, d1), toggle) in T.data.items():
            if not toggle:
                if d0 != d1:
                    return False
                else:
                    continue

            acc = AAi.acceptor(d0 * d1^(-1))
            if gap_acc is None:
                gap_acc = acc
            elif not acc.is_equivalent(gap_acc):
                return False
        return True

    def ball(self, k):
        """
        Computes the ball around `self` using words of length at most k
        """
        assert k > 1
        T = self.merge(self.inverse())
        A = T
        L = T
        for i in range(k-1):
            L = L.product(T)
            A = A.merge(L)
        return A

    def find_identities(self, max_len=10):
        """
        Searches for identities holding in the tranduction group

        Args:
            max_len: Maximium length of identities to find
        """
        T = self.ball((max_len + 1) / 2).transducer().simplification()
        identities = []
        for s in T.states():
            for a, b in itertools.combinations(s.label(), 2):
                identities.append(a.label() / b.label())

        for k, ((d0, d1), t) in self.data.items():
            if d0 == d1 and d1 == k and t == 0:
                identities.append(k)

        return identities

    def estimate_group(self, max_len=6):
        """
        Estimates the transduction group for `self`
        """
        F = self.states()[0].parent()
        identities = self.find_identities(max_len=max_len)
        G = F / identities
        return G.simplified()

    def merge(self, other):
        """
        Computes combined automata for `self` and `other`
        """
        data = copy(self.data)
        data.update(other.data)
        return BinaryInvertibleTransducer(data)

    def subautomaton(self, start):
        """
        Returns the subautomaton of the complete automaton of `self` generated
        from `start`
        """
        A = self.merge(self.inverse())
        # dfs from the start state
        data = {}
        def dfs(s):
            if s in data:
                return
            (d0, d1), t = wr(s, A)
            data[s] = (d0, d1), t
            dfs(d0)
            dfs(d1)
        dfs(start)
        return BinaryInvertibleTransducer(data)

    def principal(self):
        """
        Returns the principal automaton for the abelian transducer
        """
        assert self.is_free_abelian(), "Transducer must be abelian"
        toggles = [k for k in self.data if self.data[k][1]]
        mintoggle = min(map(lambda k: len(k.syllables()), toggles))
        for k in toggles:
            if len(k.syllables()) == mintoggle:
                (d0, d1), _ = self.data[k]
                break
        else:
            assert False, "No odd states found"

        return self.subautomaton(d0*d1^(-1))

    def extend_back(self, state):
        """
        Returns the extension of `self` with the predecessors for `state`.
        Assumes abelian.
        """
        assert state in self.data, "State " + str(state) + " doesn't exist"
        assert self.is_free_abelian(), "Not abelian"

        P = self.principal()
        for k, ((d0, d1), t) in P.data.items():
            if d1.is_one() and not d0.is_one():
                gamma = d0
                nu = k
                break
        else:
            assert False, "Couldn't find nu"

        data = copy(self.data)
        for k, ((d0, d1), t) in self.data.items():
            if t and d0 == state:
                A = self.subautomaton(k*nu^(2)).merge(self)
                return A.merge(A.subautomaton(k*nu))
            elif t and d1 == state:
                A = self.subautomaton(k*nu^(-2)).merge(self)
                return A.merge(A.subautomaton(k*nu^(-1)))
            elif not t and d0 == state:
                assert d1 == state
                A = self.subautomaton(k*nu).merge(self)
                return A.merge(A.subautomaton(k*nu^(-1)))
        return BinaryInvertibleTransducer(data)

    def grow(self):
        """
        Grows `self` by residuating each state backwards and returns the
        resulting transducer. Assumes abelian.
        """
        assert self.is_free_abelian()
        A = self
        for s in self.states():
            A = A.merge(self.extend_back(s))
        return A.minimized()

    def _ideal(self, z=None):
        """
        Computes an ideal of a multivariate polynomial ring whose solutions
        are the field representation of the free abelian machine.

        If 'z' is provided, then the polynomial ring is over z.parent()
        and 'z' is not included as a variable in the ring.
        """
        assert self.is_free_abelian(), "Transducer must be free abelian"
        var = {k: 'x%d' % i for i, k in enumerate(self.data.keys())}
        if z is None:
            R = PolynomialRing(QQ, self.n + 1, var.values() + ['z'])
            z = R('z')
        else:
            R = PolynomialRing(z.parent(), self.n, var.values())

        var = {k : R(var[k]) for k in self.data.keys()}
        polys = []
        for k, ((d0, d1), t) in self.data.items():
            if t:
                polys.append(var[k] * z  + 1 - var[d0])
                polys.append(var[k] * z - 1 - var[d1])
            else:
                polys.append(var[k] * z - var[d0])

        return Ideal(polys)

    def field_representation(self):
        """
        Computes the representation of an abelian transducer as elements over
        a finite extension of the rationals.

        Returns a tuple (F, S) where F is the base field and S is a dictionary
        mapping self.states() to elements of F
        """
        I = self._ideal()
        T = I.triangular_decomposition()[0]
        chi = T.gens()[0].univariate_polynomial()
        F = NumberField(chi, 'Z')
        solutions = self._ideal(z=F('Z')).variety()
        assert len(solutions) == 1
        return F, solutions[0]

    def digraph(self):
        """
        Returns a digraph for `self`

        Edges are labled as 0|0, 0|1, 1|0, or 1|1
        """
        edges = {}
        for k, ((d0, d1), t) in self.data.items():
            if t:
                edges[k] = {d0: '0|1', d1: '1|0'}
            else:
                edges[k] = {d0: '0|0', d1: '1|1'}
        return DiGraph(edges)

    def terminal_scc_transducers(self):
        """
        Returns the terminal strongly connected components as transducers.

        Terminal means that no transition exits the SCC, so the subautomata
        returned are complete and have one strongly connected component.
        """
        out = []
        for V in self.digraph().strongly_connected_components():
            if len(V) < 1:
                continue
            for v in V:
                transitions = self.data[v][0]
                if transitions[0] not in V or transitions[1] not in V:
                    break
            else:
              out.append(BinaryInvertibleTransducer({v: self.data[v] for v in V}))
        return out


    def plot(self, labeled=True):
        """
        Returns a graphplot object for the automaton

        Edges have the following coloring:
            0 | 0 -> black
            1 | 1 -> grey
            0 | 1 -> green
            1 | 0 -> blue
        """
        D = self.digraph()
        edge_colormap = {"0|0": "black", "1|1": "grey",
                         "0|1": "green", "1|0": "blue"}
        size = max((self.n + 1) / 2, 10)
        return D.graphplot(layout='spring', color_by_label=edge_colormap,
                           vertex_color='white', iterations=PLOT_ITERS,
                           vertex_labels=labeled, dpi=PLOT_DPI,
                           figsize=[size, size]).plot()

    def __repr__(self):
        return "Binary Invertible Transducer on {} states".format(self.n)

    def __str__(self):
        return repr(self)

class InvalidMatrix(Exception):
    pass

class MachineTooLarge(Exception):
    pass

class MatrixAutomaton(object):
    """A convenient representation of abelian transducers"""
    def __init__(self, A, r, s=None, max_size=None):
        self.A = A
        self.m = A.dimensions()[0]
        self.r = r
        if s == None:
            self.s = A.parent(1).columns()[0]
        else:
            self.s = s
        self.max_size = max_size
        # These are computed lazily
        self.edges = set()
        self.states = set()
        self.T = None
        self.PH = None

    def _traverse(self, start=None):
        """
        Traverse the transducer defined by A and r

        Return the list of edges in the form
        (u, v, a, b)
        where u,v are state vectors and the transition is of the form a | b
        """
        if start is None:
            start = self.s

        if tuple(start) not in self.states:
            A,r = self.A, self.r

            # Return if we've seen this edge
            def inn(s, c, a, b):
                return (tuple(s), tuple(c), a, b) in self.edges

            # Add the edge
            def add(s, c, a, b):
                self.states.add(tuple(c))
                self.edges.add((tuple(s), tuple(c), a, b))

            # DFS from the state s, adding all edges to the set
            def dfs(s):
                if self.max_size and len(self.states) > self.max_size:
                    raise MachineTooLarge

                e = s[0] % 2  # 0 if even, 1 if odd
                resid0, b0 = A*s + e*r, e
                resid1, b1 = A*s - e*r, 1-e

                if inn(s, resid0, 0, b0):
                    return
                add(s, resid0, 0, b0)
                add(s, resid1, 1, b1)

                dfs(resid0)
                dfs(resid1)

            # Start from s
            self.states.add(tuple(start))
            dfs(start)
        return self.edges

    def polyhedron(self):
        if self.PH is None:
            edges = map(lambda edge: edge[:2], self._traverse())
            graph = DiGraph(edges, loops=True, multiedges=True)
            self.PH = Polyhedron(vertices=graph.vertices())
        return self.PH

    def transducer(self, relabeled=True, start=None):
        """
        Returns A Transducer object for A and r.
        The initial state is s
        """
        if start is None:
            start = self.s
        if self.T is None or start != self.s:
            T = Transducer(self._traverse(start=start),
                           initial_states=[tuple(start)])
            if start == self.s:
                self.T = T
        else:
            T = self.T
        return T.relabeled() if relabeled else T

    def bit(self):
        """
        Returns `self` as a BinaryInvertibleTransducer type
        """
        return transducer_to_bit(self.transducer())

    def plot(self, **kwargs):
        """
        Returns a graphplot object for the automaton

        The start state is colored red
        Edges have the following coloring:
            copy  -> grey
            0 | 1 -> green
            1 | 0 -> blue
        """
        T = self.transducer(**kwargs)
        D = T.digraph()
        D.remove_multiple_edges()
        start = T.process([])[1].label()

        vertex_colormap = {"red": [start]}
        edge_colormap = {"0|0": "grey", "0|1":"green", "1|0":"blue"}
        return D.graphplot(layout='spring', color_by_label=edge_colormap,
                           vertex_colors=vertex_colormap, vertex_color='white',
                           iterations=1000, dpi=200).plot()

    def __str__(self):
        T = self.transducer()
        A, r = self.A, self.r
        return "{} given by characteristic polynomial {} and r = {}".format(
            T, A.charpoly(z), r)

    __repr__ = __str__


class PrincipalAutomaton(MatrixAutomaton):
    """Prinipal Automaton \mathfrak A(A)"""

    def __init__(self, A):
        cp = A.charpoly()
        if A.det() == 0:
            raise InvalidMatrix("A not invertible")
        if not cp.is_irreducible():
            raise InvalidMatrix("A.charpoly() not irreducible")
        if not all([a[0].abs() < 1.0 for a in cp.roots(ring=QQbar)]):
            raise InvalidMatrix("A not contracting")
        super(PrincipalAutomaton, self).__init__(A, A.columns()[0])
        F.<Z> = NumberField(A.charpoly(z))
        self.F = F


def transducer_to_bit(T):
    """
    Converts a transducer from sage's builtin Transducer type to
    our custom BinaryInvertibleTransducer class
    """
    states = T.states()
    data = {}
    for s in states:
        v = [[0,0], 0]
        t1, t2 = T.transitions(from_state=s)
        v[0][t1.word_in[0]] = t1.to_state
        v[0][t2.word_in[0]] = t2.to_state
        v[1] = int(t1.to_state != t2.to_state)
        data[s] = v
    return BinaryInvertibleTransducer(data, convert=True)

def CCC(n,m):
    """
    Returns the Binary Invertible Transducer for A_nm
    """
    assert m < n, "m must be less than n"
    states = range(n)
    data = {}
    data[0] = ((1, m), 1)
    for s in range(1, n):
        data[s] = (((s + 1) % n, (s + 1) % n), 0)
    return BinaryInvertibleTransducer(data, convert=True)

def lineT(*args):
    """
    Constructs a line transducer given the set of bits determining if
    each state is a toggle. The self-loop transition is always 0, and
    for the last state, it is both 0 and 1.
    """
    states = range(len(args))
    data = {}
    for s in states:
        data[s] = ((s, min(s + 1, len(args) - 1)), args[s])
    return BinaryInvertibleTransducer(data, convert=True)

def num3T(num):
    """
    Returns the transducer defined by the given number, according to
    https://arxiv.org/pdf/0803.3555.pdf
    """
    a12,a13,a22,a23,a32,a33,t1,t2,t3 = (num - 1).digits(base=3, padto=9)
    T = t1+3*t2+9*t3
    t1,t2,t3 = T.digits(base=2, padto=3)

    assert a12 + 3*a13 + 9*a22 + 27*a23 + 81*a32 + 243*a33 + \
            729*(t1 + 2*t2 + 4*t3) + 1 == num
    data = {
        0: ((a12, a13), t1),
        1: ((a22, a23), t2),
        2: ((a32, a33), t3)
    }
    return BinaryInvertibleTransducer(data, convert=True)

def spectral_radius(A):
    """
    Computes the spectral radius of the given matrix.
    The spectral radius is the largest absolute value of an eigenvalue of A.
    """
    return max(map(lambda r: r[0].abs(), A.charpoly().roots(ring=QQbar)))

def _companion_matrix(poly):
    """
    Computes the companion matrix of the polynomial.
    We use a slightly different form of the companion matrix, which has
    reversed columns and rows.
    """
    deg = poly.degree()
    B = companion_matrix(poly) # compute the usual companion matrix
    A = B[::-1, ::-1] # reverse rows and columns
    assert A.charpoly() == B.charpoly()
    return A

def random_transition_charpoly(deg):
    """
    Generates a random valid characteristic polynomial of an abelian transducer
    Such polynomials are irreducible, contracting, and monic of the form
    z^m + 1/2 g(z), where g(z) is an integer polynomial and |g(0)| = 1.
    """
    R.<z> = PolynomialRing(QQ)
    while True:
        low = -deg-1
        high = deg+1
        coefficients = random_vector(deg, x=low, y=high)
        poly = R(list(coefficients/2) + [1])

        # Check that it is irreducible and contracting
        if poly.is_irreducible():
            if all([r[0].abs() < 1.0 for r in poly.roots(ring=QQbar)]):
                return poly

def random_transition_matrix(dim):
    """
    Generates a random valid transition matrix of an abelian transducer.
    """
    assert dim >= 2
    columns = []
    return _companion_matrix(random_transition_charpoly(dim))

def random_principal_automaton(dimension):
    """
    Generates a the principal automaton (generated by e1 with r = A * e1)
    for a random transition matrix.
    """
    A = random_transition_matrix(dimension)
    AA = PrincipalAutomaton(A)
    return AA

def random_abelian_automaton(dimension, max_size=1000):
    """
    Generates a random abelian matrix automaton.
    Max number of states and be controlled with the `max_size` argument, and
    the default value is 1000.
    """
    while True:
        A = random_transition_matrix(dimension)
        v = random_vector(dimension, -dimension-1, dimension+1)
        # make v[0] odd
        v[0] = v[0] * 2 + 1
        try:
            T = MatrixAutomaton(A, A*v, max_size=max_size)
            T._traverse()
            return T
        except MachineTooLarge:
            pass

def reciprocal_poly(p):
    return (_companion_matrix(p)^(-1)).charpoly(z)

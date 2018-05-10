"""
Code implementing Binary Invertible Transducers.

Includes code to compute useful representations of Abelian transducers.
"""
from collections import deque
from sage.all import cached_method
import itertools
import operator

load("graph_loop.sage")

fst = operator.itemgetter(0)
snd = operator.itemgetter(1)

# plot settings
PLOT_DPI = 200
PLOT_ITERS = 1000

MAX_DEPTH=10000
sys.setrecursionlimit(MAX_DEPTH)

# Declare 'z'
P.<z> = PolynomialRing(QQ)

# Type of FreeGroupElements; used for assertions
FreeGroupElement = FreeGroup().gens()[0].__class__

def group_factor(f):
    """
    Compute the factorization of a free group element
    """
    layer = ([x]*c if c > 0 else [x^(-1)]*(-c) for x,c in f.syllables())
    return [x for a in layer for x in a]

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

    @cached_method
    def states(self):
        return self.data.keys()

    def wr(self, f):
        """
        Compute the wreath recursion for `f` in the transducer `self`.
        """
        s = group_factor(f)
        if len(s) == 0:
            I = self.data.keys()[0].parent(1)
            return (I, I), 0
        (d0,d1),t = self.data[s[0]]
        for x in s[1:]:
            (xd0, xd1), xt = self.data[x]
            if t:
                d0 *= xd1
                d1 *= xd0
            else:
                d0 *= xd0
                d1 *= xd1
            t = t ^^ xt
        return (d0, d1), t

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

    @cached_method
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

    @cached_method
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

    @cached_method
    def _acc_trans(self):
        g = 'g'
        acc_trans = [[g, g, i] for i in [(0,0),(0,1),(1,0),(1,1)]]
        for s, (trans, toggle) in self.data.items():
            acc_trans.append([s, trans[0], (0, int(toggle))])
            acc_trans.append([s, trans[1], (1, 1-toggle)])
            acc_trans.append([s, g, (0, 1-toggle)])
            acc_trans.append([s, g, (1, int(toggle))])
        return acc_trans

    def acceptor(self, t):
        """
        Computes the acceptor for a state t
        """
        assert t in self.data
        acc_trans = self._acc_trans()
        A = Automaton(acc_trans, initial_states=[t],
                      final_states=self.states())
        return A.accessible_components()

    @cached_method
    def inverse(self):
        def inv(w):
            ((d0, d1), t) = w
            return ((d1^(-1), d0^(-1)), t) if t else \
                   ((d0^(-1), d1^(-1)), t)
        data = {s^(-1): inv(w) for s, w in self.data.items()}
        return BinaryInvertibleTransducer(data)

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

    def gaps(self):
        """
        Return a generator for the gap values of the odd states in `self`
        """
        for s, ((d0, d1), toggle) in self.data.items():
            if toggle:
                yield d0*d1^(-1)

    def deltas(self):
        """
        Return a generator for the deltas in `self`
        """
        odds = [k for k in self.data if self.data[k][1]]
        evens = [k for k in self.data if not self.data[k][1]]

        for o, e in itertools.product(odds, evens):
            d0, d1 = self.data[o][0]
            ed = self.data[e][0][0]
            if ed == d0:
                yield e / o
            elif ed == d1:
                yield o / e

    @cached_method
    def is_free_abelian(self):
        # Free abelian transducers have nontrivial gap value
        T = self.minimized()

        # Check simple properties
        for s, ((d0, d1), toggle) in T.data.items():
            if toggle and d0 == d1:
                return False
            elif not toggle and d0 != d1:
                return False

        # Compute product automaton
        AAi = T.product(T.inverse())

        # minimize it
        S = AAi.transducer().simplification()

        # find the equivalence class containing a gap value
        gap = T.gaps().next()
        eqv_class = None
        for s in S.states():
            words = [v.label() for v in s.label()]
            if gap in words:
                eqv_class = words
                break
        else:
            raise Exception("Couldn't find gap equivalence class")

        # check that all other gaps as in the equivalence class
        for gap in T.gaps():
            if gap not in eqv_class:
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
                yield a.label() / b.label()

        for k, ((d0, d1), t) in self.data.items():
            if d0 == d1 and d1 == k and t == 0:
                yield k

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

    def is_equivalent(self, other):
        """
        Determines if `self` and `other` are equivalent Automaton
        """
        return self.digraph().is_isomorphic(other.digraph(), edge_labels=True)

    def subautomaton(self, start):
        """
        Returns the subautomaton of the complete automaton of `self` generated
        from `start`
        """
        A = self.merge(self.inverse())
        abelian = self.is_free_abelian()

        # dfs from the start state
        data = {}
        def dfs(s):
            if s in data:
                return
            (d0, d1), t = A.wr(s)

            # Optimization for abelian machines
            if abelian and not t:
                data[s] = (d0, d0), t
                dfs(d0)
            else:
                data[s] = (d0, d1), t
                dfs(d0)
                dfs(d1)
        dfs(start)
        return BinaryInvertibleTransducer(data).minimized()

    def rank(self, f):
        """
        Computes the rank (toggle distance) of f in the abelian group
        """
        assert self.is_free_abelian(), "Transducer must be abelian"
        assert f in self.data
        rank = 0
        while True:
            (d0, d1), t = self.data[f]
            # identity
            if d0 == d1 and d0 == f:
                return infinity
            elif t:
                break
            else:
                f = d0
                rank += 1
        return rank

    @cached_method
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
                delta = k
                break
        else:
            assert False, "Couldn't find delta"

        data = copy(self.data)
        for k, ((d0, d1), t) in self.data.items():
            if t and d0 == state:
                A = self.subautomaton(k*delta^(2)).merge(self)
                return A.merge(A.subautomaton(k*delta))
            elif t and d1 == state:
                A = self.subautomaton(k*delta^(-2)).merge(self)
                return A.merge(A.subautomaton(k*delta^(-1)))
            elif not t and d0 == state:
                assert d1 == state
                A = self.subautomaton(k*delta).merge(self)
                return A.merge(A.subautomaton(k*delta^(-1)))
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

    def to_matrix_automaton(self):
        """
        Returns an equivalent matrix automaton for the abelian transducer
        `self`.

        Only works for terminal SCC transducers.
        """
        # check that we're terminal SCC
        # TODO: support non-terminal SCC transducers
        assert self.terminal_scc_transducers()[0].n == self.n

        chi = T.field_representation()[0].polynomial()
        A = _companion_matrix(chi)
        D = T.digraph()

        # Find an odd generator.
        x = None
        for x in T.base_group.gens():
            if T.data[x][1]:
                break

        # Find a cycle on the generator.
        C = D.all_simple_cycles([x])[0]
        lookup = {(s,t): l for s,t,l in D.edges()}

        # Embed x as the first standard basis vector.
        e1 = vector([1] + [0]*(A.dimensions()[0] - 1))

        # Compute the cycle equation.
        rhs = (1 - A^(len(C) -1)) * e1
        v = {"0|0": 0, "1|1": 0, "0|1": 1, "1|0": -1}
        lhs = 0
        cur = x
        for s in C[1:]:
            lhs = A*lhs + v[lookup[(cur,s)]]
            cur = s

        # Solve for r
        r = lhs.inverse()*rhs
        return MatrixAutomaton(A, r, s=e1)

    @cached_method
    def transition_matrix(self):
        """
        Return the 1/2 transition matrix for the transducer `self`
        """
        states = self.states()
        M = matrix(QQ, self.n, 0)
        for s in states:
            (d0, d1), t = self.data[s]
            col = [0]*self.n
            col[states.index(d0)] += 1/2
            col[states.index(d1)] += 1/2
            M = M.augment(vector(col))
        return M

    def word_to_vec(self, word):
        """
        Return the group word as a vector over Z^n.
        Assumes `self` is abelian.
        """
        vec = vector([0] * self.n)
        states = self.states()
        for x, k in word.syllables():
            vec[states.index(x)] += k
        return vec

    def vec_to_word(self, vec):
        """
        Return the group word corresponding to `vec`.
        Assumes `self` is abelian.
        """
        assert len(vec) == self.n, "vector must have length {}".format(self.n)
        factors = map(lambda (s,c): s^c, zip(T.states(), vec))
        word = reduce(operator.mul, factors, T.base_group.one())
        return word

    def stationary_distributionn(self):
        """
        Return the stationary distribution of `self` interpreted as a markov
        chain. Only guaranteed to exist if `self` is a terminal SCC.
        """
        s = self.states()
        B = self.transition_matrix()
        v = (B - 1).right_kernel().basis()[0]
        d = dict(zip(s, v*v.denominator()))
        return d

    def poly_ideal(self, z=None):
        """
        Computes an ideal of a multivariate polynomial ring whose solutions
        are the field representation of the free abelian machine.

        If 'z' is provided, then the polynomial ring is over z.parent()
        and 'z' is not included as a variable in the ring.
        """
        assert self.is_free_abelian(), "Transducer must be free abelian"
        var = {k: "y%d" % i for i, k in enumerate(self.data.keys())}
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

        varinv = {v:k for k,v in var.items()}
        return Ideal(polys), varinv

    @cached_method
    def field_representation(self):
        """
        Computes the representation of an abelian transducer as elements over
        a finite extension of the rationals.

        Returns a tuple (F, S) where F is the base field and S is a dictionary
        mapping self.states() to elements of F
        """
        I, varinv = self.poly_ideal()
        T = I.triangular_decomposition()[0]
        chi = T.gens()[0].univariate_polynomial()
        F.<Z> = NumberField(chi)
        I, varinv = self.poly_ideal(z=Z)
        solutions = I.variety()
        assert len(solutions) == 1
        solution = {varinv[v]: s for v,s in solutions[0].items()}
        return F, solution

    @cached_method
    def fractional_ideal(self, inverse=False):
        """
        Computes the fractional ideal corresponding to the field representation
        of the abelian automaton `self`

        Args:
            inverse: if True, use the reciprocal_poly of chi instead
        """
        F, v = self.field_representation()
        if inverse:
            # interpret the field as Q[z] / (chi^(-1)(z))
            F = NumberField(reciprocal_poly(F.polynomial()), 'Z')
            v = {k: b.polynomial()(1/F('Z')) for k,b in v.items()}
        return F, Ideal(v.values())

    def is_orbit_rational(self):
        """
        Determines if the abelian transducer `self` is orbit rational.

        Requires computation of a field representation.
        """
        F, _ = self.field_representation()
        m = F.degree()
        l = m / (2 - m % 2)
        return (F('Z')^(4*l)).is_rational()

    @cached_method
    def compressed(self):
        """
        Return the compressed diagram of the abelian transducer `self`
        """
        assert self.is_free_abelian()
        edges = {}
        for k, ((d0, d1), t) in self.data.items():
            if not t:
                continue
            l = 1
            s = d0
            while not self.data[s][1]:
                l += 1
                s = self.data[s][0][0]
            edges[k] = {s : ["0 : {}".format(l)]}
            l = 1
            s = d1
            while not self.data[s][1]:
                l += 1
                s = self.data[s][0][0]
            if s in edges[k]:
                edges[k][s].append("1 : {}".format(l))
            else:
                edges[k][s] = ["1 : {}".format(l)]
        return DiGraph(edges)


    @cached_method
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

    @cached_method
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

    def plot_compressed(self):
        """
        Plots the compressed diagram for the abelian transducer `self`
        """
        D = self.compressed()
        edge_colormap = {l : ("green" if l.startswith("0") else "blue") \
                         for l in D.edge_labels()}
        size = max((D.num_verts() + 1) / 2, 10)
        return D.graphplot(layout='spring', color_by_label=edge_colormap,
                           vertex_color='white', iterations=PLOT_ITERS,
                           edge_labels=True, dpi=PLOT_DPI,
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

    @cached_method
    def _traverse(self, start=None):
        """
        Traverse the transducer defined by A and r

        Return the list of edges in the form
        (u, v, a, b)
        where u,v are state vectors and the transition is of the form a | b
        """
        if start is None:
            start = self.s

        A, r = self.A, self.r

        states = set()
        edges = set()

        # Return if we've seen this edge
        def inn(s, c, a, b):
            return (tuple(s), tuple(c), a, b) in edges

        # Add the edge
        def add(s, c, a, b):
            states.add(tuple(c))
            edges.add((tuple(s), tuple(c), a, b))

        # DFS from the state s, adding all edges to the set
        def dfs(s):
            if self.max_size and len(states) > self.max_size:
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
        states.add(tuple(start))
        dfs(start)
        return edges

    @cached_method
    def polyhedron(self):
        """
        Return a polyhedron in m dimensions defined by the states of `self`.
        """
        edges = map(lambda edge: edge[:2], self._traverse())
        graph = DiGraph(edges, loops=True, multiedges=True)
        return Polyhedron(vertices=graph.vertices())

    @cached_method
    def transducer(self, relabeled=True, start=None):
        """
        Returns A Transducer object for A and r.
        The initial state is s
        """
        if start is None:
            start = self.s
        T = Transducer(self._traverse(start=start),
                       initial_states=[tuple(start)])
        return T.relabeled() if relabeled else T

    def to_bit(self):
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

    def __repr__(self):
        A, r = self.A, self.r
        return "MatrixAutomaton(_companion_matrix({}), r=vector({}))".format(
                A.charpoly(z), r)


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

def random_binary_invertible_transducer(size):
    states = range(size)
    data = {}
    for i in states:
        d0 = randint(0, size-1)
        d1 = randint(0, size-1)
        t = randint(0, 1)
        data[i] = (randint(0, size-1), randint(0, size-1)), randint(0, 1)
    return BinaryInvertibleTransducer(data, convert=True)


def all_simple_k_toggle_sccs(num_toggles, max_copy_chain):
    """
    Generator for all simple k-toggle scc transducers, with copy chains of
    length at most `max_copy_chain`

    Here, "simple", means that copy states have only one residual. Note that
    this does not imply abelian.
    """
    choices = itertools.product(range(num_toggles), range(max_copy_chain + 1))
    toggle_choices = itertools.product(choices, repeat=2)
    base_data = {}
    for t in range(num_toggles):
        for l in range(1, max_copy_chain + 1):
            base_data[(t, l)] = ((t, l - 1), (t, l - 1)), 0

    for dts in itertools.product(toggle_choices, repeat=num_toggles):
        data = copy(base_data)
        for t in range(num_toggles):
            data[(t, 0)] = dts[t], 1
        T = BinaryInvertibleTransducer(data, convert=True).minimized()
        T = T.terminal_scc_transducers()[0]
        if sum(t for _, t in T.data.values()) == num_toggles:
            yield T

def all_abelian_sccs(num_toggles, max_copy_chain):
    """
    Return all abelian k-toggle scc transducers, with copy chains
    of length at most `max_copy_chain`.
    """
    unique = []
    def is_unique(T):
        for Tp in unique:
            if Tp.is_equivalent(T):
                return False
        unique.append(T)
        return True
    is_abelian = lambda T: T.is_free_abelian()

    filt = lambda T: is_abelian(T) and is_unique(T)
    return filter(filt, all_simple_k_toggle_sccs(num_toggles, max_copy_chain))

Grigorchuk = BinaryInvertibleTransducer({
    'a': (('e', 'e'), 1),
    'b': (('a', 'c'), 0),
    'c': (('a', 'd'), 0),
    'd': (('b', 'e'), 0),
    'e': (('e', 'e'), 0)
}, convert=True)

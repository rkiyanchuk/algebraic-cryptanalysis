# -*- coding: utf-8 -*-
r"""
Boolean Polynomial SAT-Solver

Given an ideal or polynomial system this module performs conversion to
the DIMACS CNF format, calls MiniSat2 on that input and parses the
output.

AUHTORS:

- Martin Albrecht - (2008-09) initial version
- Mate SOOS - (2010) updated version
"""

import commands

from sage.rings.polynomial.pbori import BooleanPolynomial, BooleanMonomial
from sage.misc.prandom import shuffle as do_shuffle

from sage.all import *

class ANFSatSolver(SageObject):
    """
    Solve a boolean polynomial system using MiniSat2.
    """
    def __init__(self, ring=None, cutting_num=None):
        """
        Setup the SAT-Solver and reset internal data.

        This function is also called from :meth:`__call__()` to pass
        in parameters.

        INPUT:

        - ``ring`` - a boolean polynomial ring

        - ``cuting_num`` - the cutting number ``>= 2`` (default: ``4``)

        EXAMPLE::

            sage: B = BooleanPolynomialRing(10,'x')
            sage: ANFSatSolver(B)
            ANFSatSolver(4) over Boolean PolynomialRing in x0, x1, x2, x3, x4, x5, x6, x7, x8, x9

        """
        self._i = 1 # the maximal index for literals
        self.minus = -1
        self._mon_map = []

        if hasattr(self,"_ring") and self._ring is not None:
            if ring is not None:
                assert(ring is self._ring)
        else:
            assert(ring is not None)
            self._ring = ring

        if hasattr(self,"cutting_num") and cutting_num is None:
            pass
        elif cutting_num is None:
            self.cutting_num = 4
        else:
            if cutting_num < 2:
                raise TypeError("cutting_num must be >= 2 but is %d."%(cutting_num,))
            self.cutting_num = cutting_num

        self.cnf_literal_map.clear_cache()

    def _repr_(self):
        return "ANFSatSolver(%d) over %s"%(self.cutting_num,self._ring)

    def __getattr__(self, name):
        if name == 'ring':
            return self._ring
        else:
            raise AttributeError("ANFSatSolver does not have an attribute names '%s'"%name)

    def _cnf_literal(self):
        """
        Return a new variable for the CNF formulas.

        EXAMPLE::

            sage: B.<x,y,z> = BooleanPolynomialRing()
            sage: anf2cnf = ANFSatSolver(B)
            sage: anf2cnf._cnf_literal()
            2
            sage: anf2cnf._cnf_literal()
            3

        .. note::

          Increases the internal literal counter.
        """
        self._i += 1
        return self._i-1
    
    @cached_method
    def cnf_literal_map(self, m):
        """
        Given a monomial ``m`` in a boolean polynomial ring return a
        tuple ``((i,),(c0,c1,...))`` where ``i`` is the index of the
        monomial ``m`` and ``c0,c1,...`` are clauses which encode the
        relation between the monomial ``m`` and the variables
        contained in ``m``.

        EXAMPLE::

            sage: B.<x,y,z> = BooleanPolynomialRing()
            sage: anf2cnf = ANFSatSolver(B)
            sage: anf2cnf.cnf_literal_map(B(1))
            1

            sage: anf2cnf.cnf_literal_map(x)
            2

            sage: anf2cnf.cnf_literal_map(x*y)
            (4, [(2, -4), (3, -4), (4, -2, -3)])

            sage: anf2cnf.cnf_literal_map(y)
            3

        .. note:: 
        
          May call :meth:`_cnf_literal()`
        """
        minus = self.minus
        cnf_literal_map = self.cnf_literal_map

        if isinstance(m, BooleanPolynomial):
            if len(m) == 1:
                m = m.lm()
            else:
                raise TypeError("Input must be monomial.")
        elif not isinstance(m, BooleanMonomial):
            raise TypeError("Input must be of type BooleanPolynomial.")

        if m.deg() == 0:
            # adding the clause that 1 has to be True
            monomial = self._cnf_literal()
            return monomial

        elif m.deg() == 1:
            # a variable
            monomial = self._cnf_literal()
            return monomial

        else:
            # we need to encode the relationship between the monomial
            # and its variables
            variables = [cnf_literal_map(v) for v in m.variables()]
            monomial = self._cnf_literal()

            # (a | -w) & (b | -w) & (w | -a | -b) <=> w == a*b
            this_mon_map = []
            for v in variables:
                this_mon_map.append((v, minus * monomial))
            this_mon_map.append((monomial,) + sum([(minus*v,) for v in variables],tuple()))
            self._mon_map.append([this_mon_map, ("monomial %s" % m)])

            return monomial

    @cached_function
    def cached_permutations(mylen, equal_zero):
        """
        Generates permutations for XOR clauses, such as:
        -1  1  1
         1 -1  1
         1  1 -1
        -1 -1 -1

        or, for the inverse (inverted 'equal_zero'):
        -1 -1  1
        -1  1 -1
         1 -1 -1
         1  1  1
        """
        E = []
        for numNegated in range(0, mylen+1) :
            if (((numNegated % 2) ^ ((mylen+1) % 2)) == equal_zero) : continue
            start = []
            for i in range(numNegated) :
                start.append(1)
            for i in range(mylen-numNegated) :
                start.append(-1)
            E.extend(Permutations(start))
        return E

    def _get_monomial_map(self) :
        """
        Returns the variable-to-monomial map. These essentially
        are the clauses that define the monomials
        """
        return self._mon_map

    def cnf(self, F,  shuffle=False, format='dimacs', **kwds):
        """
        Return CNF for ``F``.

        INPUT:

        - ``shuffle`` - shuffle output list (default: ``False``)

        - ``format`` - either 'dimacs' for DIMACS or ``None`` for
          tuple list (default: ``dimacs``)

        EXAMPLE:
            sage: B.<a,b,c,d> = BooleanPolynomialRing()
            sage: solver = ANFSatSolver(B)
            sage: print solver.cnf([a*b + c + 1, d + c, a + c])
            p cnf 5 9
            c ------------------------------
            c Next definition: a*b + c + 1
            -3 -4 0
            3 4 0
            c ------------------------------
            c Next definition: c + d
            4 -5 0
            -4 5 0
            c ------------------------------
            c Next definition: a + c
            1 -4 0
            -1 4 0
            c ------------------------------
            c Next definition: a*b
            1 -3 0
            2 -3 0
            3 -1 -2 0
        """
        self.__init__( **kwds)

        if get_verbose() >= 1:
            print "Parameters: c: %d, shuffle: %s"%(self.cutting_num,shuffle)

        C = []
        for f in F:
            this_c = []
            for c in self._process_polynomial(f):
                this_c.append(c)
            C.append([this_c, ("%s" % f)])

        for mono_def,mono_desc in self._mon_map :
            C.append([mono_def, mono_desc])

        if shuffle:
            do_shuffle(C)

        if format == 'dimacs':
            return self.to_dimacs(C)
        else:
            return C

    def to_dimacs(self, C):
        """
        Prints header + clause descriptions + clauses

        Calculates number of clauses and number of variables to print the
        P VARS CLAUSES
        header. Then it just prints the clauses one after the other
        """
        numVars = self._i-1
        nClauses = 0
        for clause_set, desc in C :
            nClauses += len(clause_set)

        out = ["p cnf %d %d\n"%(numVars,nClauses)]
        for clause_set, desc in C :
            out.append("c ------------------------------\n");
            out.append("c Next definition: %s\n" %  desc);
            out.extend(" ".join(map(str,clause)) + " 0\n"  for clause in clause_set)
        return "".join(out)

    def _process_polynomial(self, f):
        """
        EXAMPLE:
            sage: B.<a,b,c,d> = BooleanPolynomialRing()
            sage: solver = ANFSatSolver(B)
            sage: solver._process_polynomial(a*b + c + 1)
            [(2, -4), (3, -4), (4, -2, -3), (1,), (4, 5), (-4, -5)]
        """
        M, E = [], []
        #M is the XOR
        #E is the helper clauses (to define the monomials)
        equal_zero = True
        cnf_literal_map = self.cnf_literal_map
        for m in f:
            if (m == self._ring(1).lm()) :
                equal_zero = not equal_zero
            else :
                mbar = cnf_literal_map( m )
                M.append( mbar )

        if len(M) > self.cutting_num:
            for Mbar, this_equal_zero in self._split_xor_list(M, equal_zero):
                E.extend(self._cnf_for_xor_list(Mbar, this_equal_zero))
        else:
            E.extend( self._cnf_for_xor_list(M, equal_zero) )

        return E

    def _split_xor_list(self, monomial_list, equal_zero):
        """
        Splits a list of monomials into sublists and introduces
        connection variables. 

        INPUT:

        - ``monomial_list`` - a list of indices already registered
          with ``self``.

        EXAMPLE::

            sage: B = BooleanPolynomialRing(3,'x')
            sage: asolver = ANFSatSolver(B)
            sage: l = [asolver._cnf_literal() for _ in range(5)]; l
            [2, 3, 4, 5, 6]
            sage: asolver._split_xor_list(l)
            [[2, 3, 7], [7, 4, 5, 8], [8, 6]]
        """
        c = self.cutting_num

        nm = len(monomial_list)
        part_length =  ceil((c-2)/ZZ(nm) * nm)
        M = []

        new_variables = []
        for j in range(0, nm, part_length):
            m =  new_variables + monomial_list[j:j+part_length]
            if (j + part_length) < nm:
                new_variables = [self._cnf_literal()]
                m += new_variables
            M.append([m, equal_zero])
            equal_zero = True
        return M

    def _cnf_for_xor_list(self, M, equal_zero):
        minus = self.minus

        E = []
        ll = len( M )
        for p in self.cached_permutations(ll, equal_zero):
            E.append( sum([(p[i] * M[i],) for i in range(ll)],tuple()) )
        return E
            
    def __call__(self, F, **kwds):
        """
        EXAMPLE:
            sage: sr = mq.SR(1,1,1,4,gf2=True)
            sage: F,s = sr.polynomial_system()
            sage: B = BooleanPolynomialRing(F.ring().ngens(), F.ring().variable_names())
            sage: F = [B(f) for f in F if B(f)]
            sage: solver = ANFSatSolver(B)
            sage: solution, t = solver(F)
            sage: solution
            {k001: 0, k002: 0, s003: 1, k000: 1, k003: 0, 
             x103: 0, w100: 0, w101: 0, w102: 1, s000: 1, 
             w103: 1, s002: 1, s001: 1, x102: 1, x101: 1, 
             x100: 1, k103: 0, k101: 0, k102: 0, k100: 1}

            sage: B.ideal(F).groebner_basis()
            [k100 + k003 + 1, 
             k101 + k003, 
             k102, 
             k103 + k003, 
             x100 + 1, 
             ...
             k000 + k003 + 1, 
             k001, 
             k002 + k003]
        """
        fn = tmp_filename()
        have_poly = False

        if isinstance(F, str):
            fh = open(fn,"w")
            fh.write(self.cnf(F, format='dimacs', **kwds))
            fh.close()

        else:
            p = iter(F).next()
            if isinstance(p, BooleanPolynomial):
                have_poly = True
                self._ring = p.parent()

                fh = open(fn,"w")
                fh.write(self.cnf(F, format='dimacs', **kwds))
                fh.close()
            elif isinstance(p, tuple):
                fh = open(fn,"w")
                fh.write(self.to_dimacs(F))
                fh.close()
            else:
                raise TypeError("Type '%s' not supported."%(type(p),))

        # call MiniSat
        on = tmp_filename()
        s =  commands.getoutput("minisat2 --threads=4 %s %s"%(fn,on))

        if get_verbose() >= 2:
            print 
            print 
            print s

        s = s.splitlines()
        for l in s:
            if "CPU time" in l:
                t = float(l[l.index(":")+1:l.rindex("s")])
                break

        res =  open(on).read()
        if res.startswith("UNSAT"):
            return False, t
        res = res[4:]
        res = map(int, res.split(" "))

        # parse result
        if not have_poly:
            return res, t
        else:
            return self.map_solution_to_variables(res), t

    def map_solution_to_variables(self, res, gd=None):
        """
        """
        if gd is None:
            gens = self._ring.gens()
            gd = {}
            cnf_literal_map = self.cnf_literal_map
            for gen in gens:
                try:
                    im = cnf_literal_map(gen.lm())
                    gd[im] = gen
                except KeyError:
                    pass

        solution = {}
        for r in res:
            if abs(r) in gd:
                if r>0:
                    solution[gd[abs(r)]] = 1
                else:
                    solution[gd[abs(r)]] = 0
        return solution

def beta(F):
    B = F.ring()
    
    n = F.nvariables()
    m = F.ngens()
    k = sum([len(f) for f in F])
    d = max([f.total_degree() for f in F])
    return k / float(m * sum([binomial(n,i) for i in range(0,d+1)]))



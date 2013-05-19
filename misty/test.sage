#!/usr/bin/env sage
# -*- coding: utf-8 -*-

"""
Install `cryptominisat` extension first!
In Sage run:
    sage: install_package('cryptominisat')
Then from command promt run:
    $ sage -b
To compile the Sage extension modules.

"""

from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence
from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence_generic

from sage.sat.boolean_polynomials import solve as sat_solve


def inject(F, vars, values):
    """Inject vars values into polynomial system. """
    sub_values = dict(zip(vars, values))
    return F.subs(sub_values)


def get_vars(solution, vars):
    """Obtain variable values from solution dict. """
    values = list()
    for i in vars:
        values.append(solution[i])
    return values


load('misty.sage')
m = Misty()


def test_fl():
    m = Misty()
    plain = m._vars('IN', 32)
    key = m._vars('K', 128)
    subkeys = split(m._vars('KS', 128), 16)

    m.key = split(key, 16)

    polynomials = m.polynomials_fl(plain, subkeys, 1)
    F = PolynomialSequence(polynomials)
    F = inject(F, m._vars('IN', 32), [1]*32)
    F = inject(F, m._vars('K', 128), [1]*128)
    F = inject(F, m._vars('KS', 128), [1]*128)
    result = sat_solve(F)
    values = get_vars(result[0], m._vars('FL', 32, 1))

    plain = [1] * 32
    subkeys = [ [1]*16 ] * 8
    key = subkeys
    m.key = key
    expected = m.fl(plain, subkeys, 1)
    return values == expected

print 'Testing FL...', test_fl()

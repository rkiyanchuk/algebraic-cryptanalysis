#!/usr/bin/env sage
# coding: utf-8

from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence_generic

def inject(self, vars, values):
    sub_values = dict(zip(vars, values))
    return self.subs(sub_values)
PolynomialSequence_generic.inject = inject

def common_factors(self, vars):
    factors = dict()
    for v in vars:
        factors[v] = set()

    choose_other = lambda x, m: m[0] if x != m[0] else m[1]
    for p in self:
        for t in p:
            for f in factors:
                if t.degree() > 1:
                    monomials = t.variables()
                    if f in monomials:
                        factors[f].add(choose_other(f, monomials))
    commons = dict()
    for x in factors:
        for y in factors:
            for z in factors:
                if x != y and y != z and x != z:
                    intersect = factors[x] & factors[y] & factors[z]
                    if len(intersect) > 0:
                        commons[(x, y, z)] = intersect
                        print commons[(x, y, z)]
    return commons
PolynomialSequence_generic.common_factors = common_factors


def join_systems(mqsystems, instances):
    var_names = flatten([i.ring.variable_names() for i in instances])
    common_vars = list(set(var_names))
    common_ring = BooleanPolynomialRing(len(common_vars), common_vars, order='degrevlex')
    new_mqsystem = PolynomialSequence([], common_ring)
    for s in mqsystems:
        new_mqsystem.extend(list(s))
    return new_mqsystem


if __name__ == "__main__":

    attach gost.sage
    attach anf2cnf.py

    # solving polynomial system combine from several MQ systems with different
    # plaintext/ciphertext pairs (key variables are the same).

    nr = 7
    bs = 64
    hbs = int(bs/2)
    varnames = ['a', 'b', 'c', 'd']
    gosts = [Gost(block_size=bs, rounds=nr, key_add='mod', key_order='frw', prefix=i) for i in varnames]

    print 'constructing MQ systems...'
    mqsystems = [i.polynomial_system() for i in gosts]

    print 'generating plaintext/ciphertext data...'
    #inputs = [i.random_block() for i in gosts]
    # set inputs to have max hamming distance (will get more information about transformations)
    inputs = [[0] * bs, [1] * bs, [0, 1] * hbs, [1, 0] * hbs]
    key = gosts[0].random_key()
    outputs = [gosts[i].int2bits(gosts[i].encrypt(inputs[i], key), bs) for i in range(len(gosts))]

    print  'injecting known variables...'
    for i in range(len(mqsystems)):
        mqsystems[i] = mqsystems[i].inject(gosts[i].gen_vars(gosts[i].var_names['block'], 0), inputs[i])
        mqsystems[i] = mqsystems[i].inject(gosts[i].gen_vars(gosts[i].var_names['block'], nr), outputs[i])

    print 'combining MQ systems...'
    f = join_systems(mqsystems, gosts)

    #    print 'computing reduced basis...'
    #    b = f.ideal().interreduced_basis()
    #
    #    print 'ALL DONE'
    #    save(b, 'solution' + str(len(varnames)))

    solver = ANFSatSolver(f.ring())

    print 'converting from ANF to CNF...'
    cnf_form = solver.cnf(f, format='dimacs')
    
    fs = open('gost_r' + str(nr) + '.dmcs', 'w')
    fs.write(cnf_form)
    fs.close()

    fd = open('gost_r' + str(nr) + '.key', 'w')
    fd.write(str(key))
    fd.close()

    print 'solving MQ system...'
    s, t = solver(f)
    s = solver(f)
    print 'time: ', s[1]
    s = s[0]
    print 'DONE'

    satkey = []
    r = f.ring()
    for i in range(len(key)):
        var_names = map(str, gosts[0].gen_vars(gosts[0].var_names['key'], i))
        var_names.sort()
        var_names = map(r, var_names)
        satkey.append([s[j] for j in var_names])

    if gosts[0].int2bits(gosts[0].encrypt(inputs[0], satkey), bs) == outputs[0]:
        if key == satkey:
            print 'SUCCESS:'
            print satkey
        else:
            print 'FOUND ANOTHER KEY'
            print 'actual'
            print key
            print 'found'
            print satkey


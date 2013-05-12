#!/usr/bin/env sage
# -*- coding: utf-8 -*-

"""
MISTY block cipher polynomial system generator.

"""

__author__ = 'Ruslan Kiianchuk'
__email__ = 'ruslan.kiianchuk@gmail.com'
__version__ = '0.1'


import operator


def split(l, chunk_size):
    """Split flat list into nested lists of length `chunk_size`. If the
    `chunk_size` is not multiple of list length, the last sublist is added as
    is without padding.

    Args:
        l: List to split into chunks.
        chunk_size: Length of a single nested list.

    Returns:
        Nested list of chunks each of the length `chunk_size`.

    """
    return [l[i:i + chunk_size] for i in xrange(0, len(l), chunk_size)]


def reverse(iterable):
    return list(reversed(iterable))


def vector_do(operation, a, b):
    """Perform vector operation on two lists.

    Args:
        operation: binary operation to perform (from `operator` module).
        a: first vector.
        b: second vector.

    Example:
        vector_do(operator.__xor__, [1, 1, 1], [1, 0, 1])

    """
    return map(lambda x, y: operation(x, y), a, b)


class Misty:
    """Misty cipher class.

    All method assume to take bit sequences as input. Use `get_bits` method to
    convert integer to Misty bit sequence representation and `get_integer` to
    obtain the corresponding integer back.

    """

    def get_bits(self, integer):
        """Convert integer to crazy Misty bit ordering. """
        bytes = reverse(integer.digits(256))
        bits = [reverse(b.digits(2, padto=8)) for b in bytes]
        return flatten(bits)

    def get_integer(self, bits):
        """Convert crazy Misty bit sequence to sane ordering. """
        bytes = reverse(split(bits, 8))
        bytes = [reverse(b) for b in bytes]
        return Integer(flatten(bytes), 2)

    def __init__(self):
        self.nrounds = 8
        self.block_size = 64
        self.halfblock_size = self.block_size // 2
        self.halfblock_size_fo = self.halfblock_size // 2
        self.fi_left_size = 9
        self.fi_right_size = 7
        # Subkey type constants.
        self.KEY_KO1 = 'ko1'
        self.KEY_KO2 = 'ko2'
        self.KEY_KO3 = 'ko3'
        self.KEY_KO4 = 'ko4'
        self.KEY_KI1 = 'ki1'
        self.KEY_KI2 = 'ki2'
        self.KEY_KI3 = 'ki3'
        self.KEY_KL1 = 'kl1'
        self.KEY_KL2 = 'kl2'

    def kindex(self, subkey_type, subkeys, i):
        """Index subkey according to crazy Misty indexing rule.

        Args:
            subkey_type: string, indicating subkey type.
            subkeys: list of subkey bits (each element contains 16 subkey bits).
            i: Misty round in range 1 <= i <= 8.
        """
        if i < 1:
            raise ValueError('Subkey index must start from 1. '
                             'Got {0} instead.'.format(i))

        if subkey_type == self.KEY_KO1:
            i = i
        if subkey_type == self.KEY_KO2:
            i = i + 2
        if subkey_type == self.KEY_KO3:
            i = i + 7
        if subkey_type == self.KEY_KO4:
            i = i + 4

        if subkey_type == self.KEY_KI1:
            i = i + 5
        if subkey_type == self.KEY_KI2:
            i = i + 1
        if subkey_type == self.KEY_KI3:
            i = i + 3

        if subkey_type == self.KEY_KL1:
            if i % 2 != 0:
                i = (i + 2) // 2
            else:
                i = (i // 2) + 2
        if subkey_type == self.KEY_KL2:
            if i % 2 != 0:
                i = (i + 1) // 2 + 6
            else:
                i = (i // 2) + 4

        # Normalize index.
        while i > 8:
            i = i - 8

        return subkeys[i - 1]

    def fl(self, x, subkeys, i):
        left = x[:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        kl1 = self.kindex(self.KEY_KL1, subkeys, i)
        kl2 = self.kindex(self.KEY_KL2, subkeys, i)

        temp = vector_do(operator.__and__, left, kl1)
        right = vector_do(operator.__xor__, right, temp)

        temp = vector_do(operator.__or__, right, kl2)
        left = vector_do(operator.__xor__, left, temp)
        return left + right

    def s7(self, x):
        y = [0] * len(x)
        y[0] = x[0] ^^ x[1] & x[3] ^^ x[0] & x[3] & x[4] ^^ x[1] & x[5] ^^ x[0] & x[2] & x[5] ^^ x[4] & x[5] ^^ x[0] & x[1] & x[6] ^^ x[2] & x[6] ^^ x[0] & x[5] & x[6] ^^ x[3] & x[5] & x[6] ^^ 1
        y[1] = x[0] & x[2] ^^ x[0] & x[4] ^^ x[3] & x[4] ^^ x[1] & x[5] ^^ x[2] & x[4] & x[5] ^^ x[6] ^^ x[0] & x[6] ^^ x[3] & x[6] ^^ x[2] & x[3] & x[6] ^^ x[1] & x[4] & x[6] ^^ x[0] & x[5] & x[6] ^^ 1
        y[2] = x[1] & x[2] ^^ x[0] & x[2] & x[3] ^^ x[4] ^^ x[1] & x[4] ^^ x[0] & x[1] & x[4] ^^ x[0] & x[5] ^^ x[0] & x[4] & x[5] ^^ x[3] & x[4] & x[5] ^^ x[1] & x[6] ^^ x[3] & x[6] ^^ x[0] & x[3] & x[6] ^^ x[4] & x[6] ^^ x[2] & x[4] & x[6]
        y[3] = x[0] ^^ x[1] ^^ x[0] & x[1] & x[2] ^^ x[0] & x[3] ^^ x[2] & x[4] ^^ x[1] & x[4] & x[5] ^^ x[2] & x[6] ^^ x[1] & x[3] & x[6] ^^ x[0] & x[4] & x[6] ^^ x[5] & x[6] ^^ 1
        y[4] = x[2] & x[3] ^^ x[0] & x[4] ^^ x[1] & x[3] & x[4] ^^ x[5] ^^ x[2] & x[5] ^^ x[1] & x[2] & x[5] ^^ x[0] & x[3] & x[5] ^^ x[1] & x[6] ^^ x[1] & x[5] & x[6] ^^ x[4] & x[5] & x[6] ^^ 1
        y[5] = x[0] ^^ x[1] ^^ x[2] ^^ x[0] & x[1] & x[2] ^^ x[0] & x[3] ^^ x[1] & x[2] & x[3] ^^ x[1] & x[4] ^^ x[0] & x[2] & x[4] ^^ x[0] & x[5] ^^ x[0] & x[1] & x[5] ^^ x[3] & x[5] ^^ x[0] & x[6] ^^ x[2] & x[5] & x[6]
        y[6] = x[0] & x[1] ^^ x[3] ^^ x[0] & x[3] ^^ x[2] & x[3] & x[4] ^^ x[0] & x[5] ^^ x[2] & x[5] ^^ x[3] & x[5] ^^ x[1] & x[3] & x[5] ^^ x[1] & x[6] ^^ x[1] & x[2] & x[6] ^^ x[0] & x[3] & x[6] ^^ x[4] & x[6] ^^ x[2] & x[5] & x[6]
        return y


    def s9(self, x):
        y = [0] * len(x)
        y[0] = x[0] & x[4] ^^ x[0] & x[5] ^^ x[1] & x[5] ^^ x[1] & x[6] ^^ x[2] & x[6] ^^ x[2] & x[7] ^^ x[3] & x[7] ^^ x[3] & x[8] ^^ x[4] & x[8] ^^ 1
        y[1] = x[0] & x[2] ^^ x[3] ^^ x[1] & x[3] ^^ x[2] & x[3] ^^ x[3] & x[4] ^^ x[4] & x[5] ^^ x[0] & x[6] ^^ x[2] & x[6] ^^ x[7] ^^ x[0] & x[8] ^^ x[3] & x[8] ^^ x[5] & x[8] ^^ 1
        y[2] = x[0] & x[1] ^^ x[1] & x[3] ^^ x[4] ^^ x[0] & x[4] ^^ x[2] & x[4] ^^ x[3] & x[4] ^^ x[4] & x[5] ^^ x[0] & x[6] ^^ x[5] & x[6] ^^ x[1] & x[7] ^^ x[3] & x[7] ^^ x[8]
        y[3] = x[0] ^^ x[1] & x[2] ^^ x[2] & x[4] ^^ x[5] ^^ x[1] & x[5] ^^ x[3] & x[5] ^^ x[4] & x[5] ^^ x[5] & x[6] ^^ x[1] & x[7] ^^ x[6] & x[7] ^^ x[2] & x[8] ^^ x[4] & x[8]
        y[4] = x[1] ^^ x[0] & x[3] ^^ x[2] & x[3] ^^ x[0] & x[5] ^^ x[3] & x[5] ^^ x[6] ^^ x[2] & x[6] ^^ x[4] & x[6] ^^ x[5] & x[6] ^^ x[6] & x[7] ^^ x[2] & x[8] ^^ x[7] & x[8]
        y[5] = x[2] ^^ x[0] & x[3] ^^ x[1] & x[4] ^^ x[3] & x[4] ^^ x[1] & x[6] ^^ x[4] & x[6] ^^ x[7] ^^ x[3] & x[7] ^^ x[5] & x[7] ^^ x[6] & x[7] ^^ x[0] & x[8] ^^ x[7] & x[8]
        y[6] = x[0] & x[1] ^^ x[3] ^^ x[1] & x[4] ^^ x[2] & x[5] ^^ x[4] & x[5] ^^ x[2] & x[7] ^^ x[5] & x[7] ^^ x[8] ^^ x[0] & x[8] ^^ x[4] & x[8] ^^ x[6] & x[8] ^^ x[7] & x[8] ^^ 1
        y[7] = x[1] ^^ x[0] & x[1] ^^ x[1] & x[2] ^^ x[2] & x[3] ^^ x[0] & x[4] ^^ x[5] ^^ x[1] & x[6] ^^ x[3] & x[6] ^^ x[0] & x[7] ^^ x[4] & x[7] ^^ x[6] & x[7] ^^ x[1] & x[8] ^^ 1
        y[8] = x[0] ^^ x[0] & x[1] ^^ x[1] & x[2] ^^ x[4] ^^ x[0] & x[5] ^^ x[2] & x[5] ^^ x[3] & x[6] ^^ x[5] & x[6] ^^ x[0] & x[7] ^^ x[0] & x[8] ^^ x[3] & x[8] ^^ x[6] & x[8] ^^ 1
        return y

    def fi(self, x, ki):
        ki9 = ki[0:self.fi_left_size]
        ki7 = ki[self.fi_left_size:]

        d7 = x[0:self.fi_right_size]
        d9 = x[self.fi_right_size:]

        d9 = map(lambda a, b: a ^^ b, self.s9(d9), d7 + [0, 0])
        d7 = map(lambda a, b: a ^^ b, self.s7(d7), d9[0:self.fi_right_size])
        d7 = map(lambda a, b: a ^^ b, d7, ki7)
        d9 = map(lambda a, b: a ^^ b, d9, ki9)
        d9 = map(lambda a, b: a ^^ b, self.s9(d9), d7 + [0, 0])

        return d9 + d7

    def fo(self, x, ko, ki):
        t0 = x[self.halfblock_size_fo:]
        t1 = x[0:self.halfblock_size_fo]

        t0 = map(lambda a, b: a ^^ b, t0, ko[0])
        res = self.fi(t0, ki[0])
        t0 = map(lambda a, b: a ^^ b, res, t1)

        t1 = map(lambda a, b: a ^^ b, t1, ko[1])
        t1 = map(lambda a, b: a ^^ b, self.fi(t1, ki[1]), t0)

        t0 = map(lambda a, b: a ^^ b, t0, ko[2])
        t0 = map(lambda a, b: a ^^ b, self.fi(t0, ki[2]), t1)

        t1 = map(lambda a, b: a ^^ b, t1, ko[3])

        return t0 + t1

    def feistel_round(self, data, subkeys, i):
        d0 = data[self.halfblock_size:]
        d1 = data[0:self.halfblock_size]

        # FL1
        d0 = self.fl(d0, subkeys, i)
        # FL2
        d1 = self.fl(d1, subkeys, i + 1)

        while i > 8: i = i - 8
        # FO1
        i = i - 1  # Avoid working with 1 <= i <= 8, switch to modulo 8.
        ko = [subkeys[i % 8], subkeys[(i + 2) % 8], subkeys[(i + 7) % 8], subkeys[(i + 4) % 8]]
        ki = [subkeys[(i + 5) % 8], subkeys[(i + 1) % 8], subkeys[(i + 3) % 8]]
        d1 = map(lambda a, b: a ^^ b, self.fo(d0, ko, ki), d1)

        ## FO2
        i = (i + 1) % 8  # Increase for next pseudo-round.
        ko = [subkeys[i % 8], subkeys[(i + 2) % 8], subkeys[(i + 7) % 8], subkeys[(i + 4) % 8]]
        ki = [subkeys[(i + 5) % 8], subkeys[(i + 1) % 8], subkeys[(i + 3) % 8]]
        d0 = map(lambda a, b: a ^^ b, self.fo(d1, ko, ki), d0)

        return d0 + d1

    def encipher(self, data, key):
        data = self.reorder(data)
        subkeys = self.key_schedule(key)
        for i in range(1, self.nrounds + 1, 2):
            data = self.feistel_round(data, subkeys, i)

        d0 = data[self.halfblock_size:]
        d1 = data[0:self.halfblock_size]
        # FL1
        d0 = self.fl(d0, subkeys, self.nrounds + 1)
        # FL2
        d1 = self.fl(d1, subkeys, self.nrounds + 2)
        return d0 + d1

    def key_schedule(self, key):
        k = self.reorder(key)
        key_chunks = split(k, 16)

        subkeys = list()
        for k in range(len(key_chunks)):
            if k < 7:
                subkeys.append(self.fi(key_chunks[k], key_chunks[k + 1]))
            else:
                subkeys.append(self.fi(key_chunks[k], key_chunks[0]))
        return subkeys


    def _varformatstr(self, name):
        """Prepare formatting string for variables notation.

        Args:
            name: Variable identificator string (usually one letter for
                simplicity).

        Returns:
            String that contains the variable identificator appended with
            format specificators to contains round number and block bit number.
            For instance, if max(len(Nr), len(Bs)) = 3, then string
            K03d%03d is returned.

        """
        l = str(max([len(str(self.nrounds)), len(str(self.block_size - 1))]))
        return name + "%0" + l + "d" + "%0" + l + "d"

    def _varstrs(self, name, round):
        """Create a list of variables set for a fixed round.

        Given a variable name, return list of all such variables in current
        round for specific block size.

        Args:
            name: Variable identificator string (usually one letter for

            round: Number of the enciphering round for correct variable
                numbering.

        Returns:
            List of numbered variables.

        """
        s = self._varformatstr(name)
        if s.startswith(self.var_names['block']):
            # X is a variable for plaintexts and ciphertexts, so it has the
            # size of the cipher block.
            return [s % (round, i) for i in range(self.block_size)]
        else:
            # Rest of the variables are used in Feistel Network and have half
            # size of the cipher block.
            return [s % (round, i) for i in range(self.halfblock_size)]

    def gen_vars(self, name, round_):
        """Generate variables set for given round number."""
        return [self.ring(e) for e in self._varstrs(name, round_)]

#!/usr/bin/env sage
# -*- coding: utf-8 -*-

"""
MISTY block cipher polynomial system generator.

"""

__author__ = 'Ruslan Kiianchuk'
__email__ = 'ruslan.kiianchuk@gmail.com'
__version__ = '0.9'


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

    Returns:
        Resulting vector (represented as list).

    Example:
        vector_do(operator.__xor__, [1, 1, 1], [1, 0, 1])

    """
    return map(lambda x, y: operation(x, y), a, b)


class Misty(object):
    """Misty cipher class.

    All method assume to take bit sequences as input. Use `get_bits` method to
    convert integer to Misty bit sequence representation and `get_integer` to
    obtain the corresponding integer back.

    """

    def get_bits(self, integer, nbytes=0):
        """Convert integer to crazy Misty bit ordering. """
        bytes = reverse(integer.digits(256, padto=nbytes))
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
            subkeys: list of subkey bits (each element contains 16 subkey
                bits).
            i: Misty round in range 1 <= i <= 8.

        Returns:
            16-bit subkey for corresponding index.
        """
        if i < 1:
            raise ValueError('Subkey index must start from 1. '
                             'Got {0} instead.'.format(i))

        def normalize(x):
            while x > 8:
                x = x - 8
            return x

        if subkey_type == self.KEY_KO1:
            return self.key[i - 1]
        if subkey_type == self.KEY_KO2:
            i = normalize(i + 2)
            return self.key[i - 1]
        if subkey_type == self.KEY_KO3:
            i = normalize(i + 7)
            return self.key[i - 1]
        if subkey_type == self.KEY_KO4:
            i = normalize(i + 4)
            return self.key[i - 1]
        if subkey_type == self.KEY_KI1:
            i = normalize(i + 5)
            return subkeys[i - 1]
        if subkey_type == self.KEY_KI2:
            i = normalize(i + 1)
            return subkeys[i - 1]
        if subkey_type == self.KEY_KI3:
            i = normalize(i + 3)
            return subkeys[i - 1]

        if subkey_type == self.KEY_KL1:
            if i % 2 != 0:
                i = normalize((i + 1) // 2)
                return self.key[i - 1]
            else:
                i = normalize((i // 2) + 2)
                return subkeys[i - 1]
        if subkey_type == self.KEY_KL2:
            if i % 2 != 0:
                i = normalize((i + 1) // 2 + 6)
                return subkeys[i - 1]
            else:
                i = normalize((i // 2) + 4)
                return self.key[i - 1]

    def fi(self, x, subkey_ki):
        """Misty FI function.

        Args:
            x: 16-bit input value.
            subkey_ki: 16-bit KI key chunk for FI function.

        Returns: 16-bit output of FI function.

        """
        ki7 = subkey_ki[0:self.fi_right_size]
        ki9 = subkey_ki[self.fi_right_size:]

        d9 = x[0:self.fi_left_size]
        d7 = x[self.fi_left_size:]

        d9 = vector_do(operator.__xor__, self.s9(d9), [0, 0] + d7)
        d7 = vector_do(operator.__xor__, self.s7(d7), d9[2:self.fi_left_size])
        d7 = vector_do(operator.__xor__, d7, ki7)
        d9 = vector_do(operator.__xor__, d9, ki9)
        d9 = vector_do(operator.__xor__, self.s9(d9), [0, 0] + d7)
        return d7 + d9

    def key_schedule(self, key):
        key_chunks = split(key, 16)
        self.key = key_chunks

        subkeys = list()
        for k in range(len(key_chunks)):
            if k < 7:
                subkeys.append(self.fi(key_chunks[k], key_chunks[k + 1]))
            else:
                subkeys.append(self.fi(key_chunks[k], key_chunks[0]))
        return subkeys

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
        x = reverse(x)
        y = [0] * len(x)
        y[0] = x[0] ^^ x[1] & x[3] ^^ x[0] & x[3] & x[4] ^^ x[1] & x[5] ^^ x[0] & x[2] & x[5] ^^ x[4] & x[5] ^^ x[0] & x[1] & x[6] ^^ x[2] & x[6] ^^ x[0] & x[5] & x[6] ^^ x[3] & x[5] & x[6] ^^ 1
        y[1] = x[0] & x[2] ^^ x[0] & x[4] ^^ x[3] & x[4] ^^ x[1] & x[5] ^^ x[2] & x[4] & x[5] ^^ x[6] ^^ x[0] & x[6] ^^ x[3] & x[6] ^^ x[2] & x[3] & x[6] ^^ x[1] & x[4] & x[6] ^^ x[0] & x[5] & x[6] ^^ 1
        y[2] = x[1] & x[2] ^^ x[0] & x[2] & x[3] ^^ x[4] ^^ x[1] & x[4] ^^ x[0] & x[1] & x[4] ^^ x[0] & x[5] ^^ x[0] & x[4] & x[5] ^^ x[3] & x[4] & x[5] ^^ x[1] & x[6] ^^ x[3] & x[6] ^^ x[0] & x[3] & x[6] ^^ x[4] & x[6] ^^ x[2] & x[4] & x[6]
        y[3] = x[0] ^^ x[1] ^^ x[0] & x[1] & x[2] ^^ x[0] & x[3] ^^ x[2] & x[4] ^^ x[1] & x[4] & x[5] ^^ x[2] & x[6] ^^ x[1] & x[3] & x[6] ^^ x[0] & x[4] & x[6] ^^ x[5] & x[6] ^^ 1
        y[4] = x[2] & x[3] ^^ x[0] & x[4] ^^ x[1] & x[3] & x[4] ^^ x[5] ^^ x[2] & x[5] ^^ x[1] & x[2] & x[5] ^^ x[0] & x[3] & x[5] ^^ x[1] & x[6] ^^ x[1] & x[5] & x[6] ^^ x[4] & x[5] & x[6] ^^ 1
        y[5] = x[0] ^^ x[1] ^^ x[2] ^^ x[0] & x[1] & x[2] ^^ x[0] & x[3] ^^ x[1] & x[2] & x[3] ^^ x[1] & x[4] ^^ x[0] & x[2] & x[4] ^^ x[0] & x[5] ^^ x[0] & x[1] & x[5] ^^ x[3] & x[5] ^^ x[0] & x[6] ^^ x[2] & x[5] & x[6]
        y[6] = x[0] & x[1] ^^ x[3] ^^ x[0] & x[3] ^^ x[2] & x[3] & x[4] ^^ x[0] & x[5] ^^ x[2] & x[5] ^^ x[3] & x[5] ^^ x[1] & x[3] & x[5] ^^ x[1] & x[6] ^^ x[1] & x[2] & x[6] ^^ x[0] & x[3] & x[6] ^^ x[4] & x[6] ^^ x[2] & x[5] & x[6]
        return reverse(y)

    def s9(self, x):
        x = reverse(x)
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
        return reverse(y)

    def fo(self, x, subkeys, i):
        left = x[0:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        ki1 = self.kindex(self.KEY_KI1, subkeys, i)
        ki2 = self.kindex(self.KEY_KI2, subkeys, i)
        ki3 = self.kindex(self.KEY_KI3, subkeys, i)

        ko1 = self.kindex(self.KEY_KO1, subkeys, i)
        ko2 = self.kindex(self.KEY_KO2, subkeys, i)
        ko3 = self.kindex(self.KEY_KO3, subkeys, i)
        ko4 = self.kindex(self.KEY_KO4, subkeys, i)

        left = vector_do(operator.__xor__, left, ko1)
        temp = self.fi(left, ki1)
        left = vector_do(operator.__xor__, temp, right)

        right = vector_do(operator.__xor__, right, ko2)
        temp = self.fi(right, ki2)
        right = vector_do(operator.__xor__, left, temp)

        left = vector_do(operator.__xor__, left, ko3)
        temp = self.fi(left, ki3)
        left = vector_do(operator.__xor__, temp, right)

        right = vector_do(operator.__xor__, right, ko4)

        return right + left

    def feistel_round(self, data, subkeys, i):
        left = data[0:self.halfblock_size]
        right = data[self.halfblock_size:]

        # FL1
        left = self.fl(left, subkeys, i)
        # FL2
        right = self.fl(right, subkeys, i + 1)

        # FO1
        temp = self.fo(left, subkeys, i)
        right = vector_do(operator.__xor__, right, temp)

        # FO2
        temp = self.fo(right, subkeys, i + 1)
        left = vector_do(operator.__xor__, temp, left)

        return left + right

    def encipher(self, data, key):
        subkeys = self.key_schedule(key)
        for i in range(1, self.nrounds + 1, 2):
            data = self.feistel_round(data, subkeys, i)

        left = data[0:self.halfblock_size]
        right = data[self.halfblock_size:]
        # FL n+1
        left = self.fl(left, subkeys, self.nrounds + 1)
        # FL n+2
        right = self.fl(right, subkeys, self.nrounds + 2)
        return right + left

    def selftest(self):
        """Check Misty test vectors compliance."""
        c = self.encipher(self.get_bits(0x0123456789ABCDEF, 8),
                          self.get_bits(0x00112233445566778899AABBCCDDEEFF, 16))
        res = self.get_integer(c)
        expected = 0x8b1da5f56ab3d07c
        print res == expected

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

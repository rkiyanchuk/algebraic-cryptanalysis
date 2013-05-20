#!/usr/bin/env sage
# -*- coding: utf-8 -*-

"""
MISTY block cipher polynomial system generator.

"""

__author__ = 'Ruslan Kiianchuk'
__email__ = 'ruslan.kiianchuk@gmail.com'
__version__ = '0.9'


import operator

from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence


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
    """Return reversed iterable as list."""
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
    if operation is operator.__xor__:
        if is_constant(a) and is_constant(b):
            return map(lambda x, y: operation(x, y), a, b)
        else:
            # Process variables over Boolean Polynomial Ring correctly.
            return map(lambda x, y: operator.__add__(x, y), a, b)
    elif operation is operator.__and__:
        if is_constant(a) and is_constant(b):
            return map(lambda x, y: operation(x, y), a, b)
        else:
            # Process variables over Boolean Polynomial Ring correctly.
            return map(lambda x, y: operator.__mul__(x, y), a, b)
    elif operation is operator.__or__:
        if is_constant(a) and is_constant(b):
            return map(lambda x, y: operation(x, y), a, b)
        else:
            # Process variables over Boolean Polynomial Ring correctly.
            return map(lambda x, y: x * y + x + y, a, b)
    else:
        return map(lambda x, y: operation(x, y), a, b)


def is_constant(vals):
    return all([isinstance(i, Integer) for i in vals])


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
        """Create Misty cipher object.

        It's a full scale cipher as well as its polynomial system generator.

        """
        self.nrounds = 8
        self.block_size = 64
        self.halfblock_size = self.block_size // 2
        self.halfblock_size_fo = self.halfblock_size // 2
        self.fi_left_size = 9
        self.fi_right_size = 7
        self.key = None
        self.subkeys = None
        self.gen_ring()
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

    def kindex(self, subkey_type, i):
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
            return self.subkeys[i - 1]
        if subkey_type == self.KEY_KI2:
            i = normalize(i + 1)
            return self.subkeys[i - 1]
        if subkey_type == self.KEY_KI3:
            i = normalize(i + 3)
            return self.subkeys[i - 1]

        if subkey_type == self.KEY_KL1:
            if i % 2 != 0:
                i = normalize((i + 1) // 2)
                return self.key[i - 1]
            else:
                i = normalize((i // 2) + 2)
                return self.subkeys[i - 1]
        if subkey_type == self.KEY_KL2:
            if i % 2 != 0:
                i = normalize((i + 1) // 2 + 6)
                return self.subkeys[i - 1]
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
        """Generate subkeys according to Misty key schedule algorithm.

        Args:
            key: List of 128 bits.

        Returns:
            List of 8 subkeys (each containing list of 16 bits).
        """
        key_chunks = split(key, 16)
        self.key = key_chunks

        subkeys = list()
        for k in range(len(key_chunks)):
            if k < 7:
                subkeys.append(self.fi(key_chunks[k], key_chunks[k + 1]))
            else:
                subkeys.append(self.fi(key_chunks[k], key_chunks[0]))
        self.subkeys = subkeys
        return subkeys

    def fl(self, x, i):
        """Misty key injection FL function.

        Args:
            x: 32-bit input.
            i: number of round.

        Returns:
            Resulting 32 bits after key injection.

        """
        left = x[:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        kl1 = self.kindex(self.KEY_KL1, i)
        kl2 = self.kindex(self.KEY_KL2, i)

        temp = vector_do(operator.__and__, left, kl1)
        right = vector_do(operator.__xor__, right, temp)

        temp = vector_do(operator.__or__, right, kl2)
        left = vector_do(operator.__xor__, left, temp)
        return left + right

    def s7(self, x, r=None):
        """Substitute with Misty S7 SBox.

        Bit ordering is reversed due to Crazy Misty Spec bit ordering.
        """
        y = [0] * len(x)
        if not r:
            y[6] = x[6] ^^ x[5] &  x[3] ^^ x[6] &  x[3] &  x[2] ^^ x[5] &  x[1] ^^ x[6] &  x[4] &  x[1] ^^ x[2] &  x[1] ^^ x[6] &  x[5] &  x[0] ^^ x[4] &  x[0] ^^ x[6] &  x[1] &  x[0] ^^ x[3] &  x[1] &  x[0] ^^ 1
            y[5] = x[6] &  x[4] ^^ x[6] &  x[2] ^^ x[3] &  x[2] ^^ x[5] &  x[1] ^^ x[4] &  x[2] &  x[1] ^^ x[0] ^^ x[6] &  x[0] ^^ x[3] &  x[0] ^^ x[4] &  x[3] &  x[0] ^^ x[5] &  x[2] &  x[0] ^^ x[6] &  x[1] &  x[0] ^^ 1
            y[4] = x[5] &  x[4] ^^ x[6] &  x[4] &  x[3] ^^ x[2] ^^ x[5] &  x[2] ^^ x[6] &  x[5] &  x[2] ^^ x[6] &  x[1] ^^ x[6] &  x[2] &  x[1] ^^ x[3] &  x[2] &  x[1] ^^ x[5] &  x[0] ^^ x[3] &  x[0] ^^ x[6] &  x[3] &  x[0] ^^ x[2] &  x[0] ^^ x[4] &  x[2] &  x[0]
            y[3] = x[6] ^^ x[5] ^^ x[6] &  x[5] &  x[4] ^^ x[6] &  x[3] ^^ x[4] &  x[2] ^^ x[5] &  x[2] &  x[1] ^^ x[4] &  x[0] ^^ x[5] &  x[3] &  x[0] ^^ x[6] &  x[2] &  x[0] ^^ x[1] &  x[0] ^^ 1
            y[2] = x[4] &  x[3] ^^ x[6] &  x[2] ^^ x[5] &  x[3] &  x[2] ^^ x[1] ^^ x[4] &  x[1] ^^ x[5] &  x[4] &  x[1] ^^ x[6] &  x[3] &  x[1] ^^ x[5] &  x[0] ^^ x[5] &  x[1] &  x[0] ^^ x[2] &  x[1] &  x[0] ^^ 1
            y[1] = x[6] ^^ x[5] ^^ x[4] ^^ x[6] &  x[5] &  x[4] ^^ x[6] &  x[3] ^^ x[5] &  x[4] &  x[3] ^^ x[5] &  x[2] ^^ x[6] &  x[4] &  x[2] ^^ x[6] &  x[1] ^^ x[6] &  x[5] &  x[1] ^^ x[3] &  x[1] ^^ x[6] &  x[0] ^^ x[4] &  x[1] &  x[0]
            y[0] = x[6] &  x[5] ^^ x[3] ^^ x[6] &  x[3] ^^ x[4] &  x[3] &  x[2] ^^ x[6] &  x[1] ^^ x[4] &  x[1] ^^ x[3] &  x[1] ^^ x[5] &  x[3] &  x[1] ^^ x[5] &  x[0] ^^ x[5] &  x[4] &  x[0] ^^ x[6] &  x[3] &  x[0] ^^ x[2] &  x[0] ^^ x[4] &  x[1] &  x[0]
        else:
            # Process variables over Boolean Polynomial Ring correctly.
            return [
            r[6] + x[6] + x[5] * x[3] + x[6] * x[3] * x[2] + x[5] * x[1] + x[6] * x[4] * x[1] + x[2] * x[1] + x[6] * x[5] * x[0] + x[4] * x[0] + x[6] * x[1] * x[0] + x[3] * x[1] * x[0] + 1,
            r[5] + x[6] * x[4] + x[6] * x[2] + x[3] * x[2] + x[5] * x[1] + x[4] * x[2] * x[1] + x[0] + x[6] * x[0] + x[3] * x[0] + x[4] * x[3] * x[0] + x[5] * x[2] * x[0] + x[6] * x[1] * x[0] + 1,
            r[4] + x[5] * x[4] + x[6] * x[4] * x[3] + x[2] + x[5] * x[2] + x[6] * x[5] * x[2] + x[6] * x[1] + x[6] * x[2] * x[1] + x[3] * x[2] * x[1] + x[5] * x[0] + x[3] * x[0] + x[6] * x[3] * x[0] + x[2] * x[0] + x[4] * x[2] * x[0],
            r[3] + x[6] + x[5] + x[6] * x[5] * x[4] + x[6] * x[3] + x[4] * x[2] + x[5] * x[2] * x[1] + x[4] * x[0] + x[5] * x[3] * x[0] + x[6] * x[2] * x[0] + x[1] * x[0] + 1,
            r[2] + x[4] * x[3] + x[6] * x[2] + x[5] * x[3] * x[2] + x[1] + x[4] * x[1] + x[5] * x[4] * x[1] + x[6] * x[3] * x[1] + x[5] * x[0] + x[5] * x[1] * x[0] + x[2] * x[1] * x[0] + 1,
            r[1] + x[6] + x[5] + x[4] + x[6] * x[5] * x[4] + x[6] * x[3] + x[5] * x[4] * x[3] + x[5] * x[2] + x[6] * x[4] * x[2] + x[6] * x[1] + x[6] * x[5] * x[1] + x[3] * x[1] + x[6] * x[0] + x[4] * x[1] * x[0],
            r[0] + x[6] * x[5] + x[3] + x[6] * x[3] + x[4] * x[3] * x[2] + x[6] * x[1] + x[4] * x[1] + x[3] * x[1] + x[5] * x[3] * x[1] + x[5] * x[0] + x[5] * x[4] * x[0] + x[6] * x[3] * x[0] + x[2] * x[0] + x[4] * x[1] * x[0]
            ]
        return y

    def s9(self, x, r=None):
        """Substitute with Misty S9 SBox. """
        y = [0] * len(x)
        if not r:
            y[8] = x[8] &  x[4] ^^ x[8] &  x[3] ^^ x[7] &  x[3] ^^ x[7] &  x[2] ^^ x[6] &  x[2] ^^ x[6] &  x[1] ^^ x[5] &  x[1] ^^ x[5] &  x[0] ^^ x[4] &  x[0] ^^ 1
            y[7] = x[8] &  x[6] ^^ x[5] ^^ x[7] &  x[5] ^^ x[6] &  x[5] ^^ x[5] &  x[4] ^^ x[4] &  x[3] ^^ x[8] &  x[2] ^^ x[6] &  x[2] ^^ x[1] ^^ x[8] &  x[0] ^^ x[5] &  x[0] ^^ x[3] &  x[0] ^^ 1
            y[6] = x[8] &  x[7] ^^ x[7] &  x[5] ^^ x[4] ^^ x[8] &  x[4] ^^ x[6] &  x[4] ^^ x[5] &  x[4] ^^ x[4] &  x[3] ^^ x[8] &  x[2] ^^ x[3] &  x[2] ^^ x[7] &  x[1] ^^ x[5] &  x[1] ^^ x[0]
            y[5] = x[8] ^^ x[7] &  x[6] ^^ x[6] &  x[4] ^^ x[3] ^^ x[7] &  x[3] ^^ x[5] &  x[3] ^^ x[4] &  x[3] ^^ x[3] &  x[2] ^^ x[7] &  x[1] ^^ x[2] &  x[1] ^^ x[6] &  x[0] ^^ x[4] &  x[0]
            y[4] = x[7] ^^ x[8] &  x[5] ^^ x[6] &  x[5] ^^ x[8] &  x[3] ^^ x[5] &  x[3] ^^ x[2] ^^ x[6] &  x[2] ^^ x[4] &  x[2] ^^ x[3] &  x[2] ^^ x[2] &  x[1] ^^ x[6] &  x[0] ^^ x[1] &  x[0]
            y[3] = x[6] ^^ x[8] &  x[5] ^^ x[7] &  x[4] ^^ x[5] &  x[4] ^^ x[7] &  x[2] ^^ x[4] &  x[2] ^^ x[1] ^^ x[5] &  x[1] ^^ x[3] &  x[1] ^^ x[2] &  x[1] ^^ x[8] &  x[0] ^^ x[1] &  x[0]
            y[2] = x[8] &  x[7] ^^ x[5] ^^ x[7] &  x[4] ^^ x[6] &  x[3] ^^ x[4] &  x[3] ^^ x[6] &  x[1] ^^ x[3] &  x[1] ^^ x[0] ^^ x[8] &  x[0] ^^ x[4] &  x[0] ^^ x[2] &  x[0] ^^ x[1] &  x[0] ^^ 1
            y[1] = x[7] ^^ x[8] &  x[7] ^^ x[7] &  x[6] ^^ x[6] &  x[5] ^^ x[8] &  x[4] ^^ x[3] ^^ x[7] &  x[2] ^^ x[5] &  x[2] ^^ x[8] &  x[1] ^^ x[4] &  x[1] ^^ x[2] &  x[1] ^^ x[7] &  x[0] ^^ 1
            y[0] = x[8] ^^ x[8] &  x[7] ^^ x[7] &  x[6] ^^ x[4] ^^ x[8] &  x[3] ^^ x[6] &  x[3] ^^ x[5] &  x[2] ^^ x[3] &  x[2] ^^ x[8] &  x[1] ^^ x[8] &  x[0] ^^ x[5] &  x[0] ^^ x[2] &  x[0] ^^ 1
            return y
        else:
            # Process variables over Boolean Polynomial Ring correctly.
            return [
            r[8] + x[8] * x[4] + x[8] * x[3] + x[7] * x[3] + x[7] * x[2] + x[6] * x[2] + x[6] * x[1] + x[5] * x[1] + x[5] * x[0] + x[4] * x[0] + 1,
            r[7] + x[8] * x[6] + x[5] + x[7] * x[5] + x[6] * x[5] + x[5] * x[4] + x[4] * x[3] + x[8] * x[2] + x[6] * x[2] + x[1] + x[8] * x[0] + x[5] * x[0] + x[3] * x[0] + 1,
            r[6] + x[8] * x[7] + x[7] * x[5] + x[4] + x[8] * x[4] + x[6] * x[4] + x[5] * x[4] + x[4] * x[3] + x[8] * x[2] + x[3] * x[2] + x[7] * x[1] + x[5] * x[1] + x[0],
            r[5] + x[8] + x[7] * x[6] + x[6] * x[4] + x[3] + x[7] * x[3] + x[5] * x[3] + x[4] * x[3] + x[3] * x[2] + x[7] * x[1] + x[2] * x[1] + x[6] * x[0] + x[4] * x[0],
            r[4] + x[7] + x[8] * x[5] + x[6] * x[5] + x[8] * x[3] + x[5] * x[3] + x[2] + x[6] * x[2] + x[4] * x[2] + x[3] * x[2] + x[2] * x[1] + x[6] * x[0] + x[1] * x[0],
            r[3] + x[6] + x[8] * x[5] + x[7] * x[4] + x[5] * x[4] + x[7] * x[2] + x[4] * x[2] + x[1] + x[5] * x[1] + x[3] * x[1] + x[2] * x[1] + x[8] * x[0] + x[1] * x[0],
            r[2] + x[8] * x[7] + x[5] + x[7] * x[4] + x[6] * x[3] + x[4] * x[3] + x[6] * x[1] + x[3] * x[1] + x[0] + x[8] * x[0] + x[4] * x[0] + x[2] * x[0] + x[1] * x[0] + 1,
            r[1] + x[7] + x[8] * x[7] + x[7] * x[6] + x[6] * x[5] + x[8] * x[4] + x[3] + x[7] * x[2] + x[5] * x[2] + x[8] * x[1] + x[4] * x[1] + x[2] * x[1] + x[7] * x[0] + 1,
            r[0] + x[8] + x[8] * x[7] + x[7] * x[6] + x[4] + x[8] * x[3] + x[6] * x[3] + x[5] * x[2] + x[3] * x[2] + x[8] * x[1] + x[8] * x[0] + x[5] * x[0] + x[2] * x[0] + 1
            ]

    def fo(self, x, i):
        """Misty FO function.

        Second level nested Feistel network.

        Args:
            x: 32-bit input list.
            i: number of rounds.

        Returns:
            Resulting bits list.
        """


        left = x[0:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        ki1 = self.kindex(self.KEY_KI1, i)
        ki2 = self.kindex(self.KEY_KI2, i)
        ki3 = self.kindex(self.KEY_KI3, i)

        ko1 = self.kindex(self.KEY_KO1, i)
        ko2 = self.kindex(self.KEY_KO2, i)
        ko3 = self.kindex(self.KEY_KO3, i)
        ko4 = self.kindex(self.KEY_KO4, i)

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

    def feistel_round(self, data, i):
        """Misty Feistel network single run.

        It actually performs first 2 rounds (look for Misty specs).

        Args:
            data: 64-bit input list.
            i: number of actual round (pay attention to indices according
                to Misty specification). Rounds are in range 1 <= i <= n + 2,
                where `n` is total number of rounds
        Returns:
            Resulting 64-bit list.

        """
        left = data[0:self.halfblock_size]
        right = data[self.halfblock_size:]

        # FL1
        left = self.fl(left, i)
        # FL2
        right = self.fl(right, i + 1)

        # FO1
        temp = self.fo(left, i)
        right = vector_do(operator.__xor__, right, temp)

        # FO2
        temp = self.fo(right, i + 1)
        left = vector_do(operator.__xor__, temp, left)

        return left + right

    def encipher(self, data, key):
        """Encipher plaintext with Misty cryptoalgorithm.

        Args:
            data: 64-bit input list (plaintext).
            key: 128-bit input list (key).

        Returns:
            64-bit list (ciphertext).

        """
        for i in range(1, self.nrounds + 1, 2):
            data = self.feistel_round(data, i)

        left = data[0:self.halfblock_size]
        right = data[self.halfblock_size:]
        # FL n+1
        left = self.fl(left, self.nrounds + 1)
        # FL n+2
        right = self.fl(right, self.nrounds + 2)
        return right + left

    def selftest(self):
        """Check Misty test vectors compliance."""
        plaintext = 0x0123456789ABCDEF
        key = 0x00112233445566778899AABBCCDDEEFF
        self.key_schedule(self.get_bits(key, 16))
        c = self.encipher(self.get_bits(plaintext, 8),
                          self.get_bits(key, 16))
        result = self.get_integer(c)
        expected = 0x8b1da5f56ab3d07c
        return result == expected

    ###########################################################################
    # POLYNOMIAL SYSTEM
    ###########################################################################

    def _varformatstr(self, name):
        """Prepare formatting string for variables notation.

        Args:
            name: Variable identificator string.

        Returns:
            Variable identificator string appended with format specificators
            that contains round number and block bit number.
            Format: R<round number>_<var id>_<bit number>

        """
        l = str(len(str(self.block_size - 1)))
        return "R%s_" + name + "_%0" + l + "d"

    def _varstrs(self, name, nbits, round=''):
        """Construct strings with variables names.

        Args:
            name: variable string identificator.
            nbits: number of variables set of the same type.
            round: number of round for which variables are defined. If not
                specified, no round prefix is prepended to the string.

        Returns:
            List of strings with variables names.

        """
        s = self._varformatstr(name)
        round = str(round)
        if not round:
            # Exclude round prefix.
            s = s[s.find('_') + 1:]
            return [s % (i) for i in range(nbits)]
        return [s % (round, i) for i in range(nbits)]

    def _vars(self, name, nbits, round=''):
        """Construct variables in predefined Misty ring.

        Refer to `_varstrs()` and `gen_ring()` for details.

        """
        var_names = self._varstrs(name, nbits, round)
        return [self.ring(e) for e in var_names]

    def gen_round_var_names(self, round):
        """Generate variables names set for given round number."""
        var_names = list()
        # FL
        var_names += self._varstrs('FL_KL1', 16, round)
        var_names += self._varstrs('FL_KL2', 16, round)
        var_names += self._varstrs('FL_XOR', 16, round)
        var_names += self._varstrs('FL', 32, round)
        # FI
        for i in range(1, 4):
            # FI has 3 subrounds in FO function.
            var_names += self._varstrs('FI' + str(i), 16, round)
            var_names += self._varstrs('FI' + str(i) + '_S9', 9, round)
            var_names += self._varstrs('FI' + str(i) + '_S7', 7, round)
            var_names += self._varstrs('FI' + str(i) + '_SS9', 9, round)
            var_names += self._varstrs('FI' + str(i) + '_KI2', 16, round)
        # FO
        var_names += self._varstrs('FO', 32, round)
        var_names += self._varstrs('FO_KO1', 16, round)
        var_names += self._varstrs('FO_KO2', 16, round)
        var_names += self._varstrs('FO_KO3', 16, round)


        return var_names

    def gen_ring(self):
        """Generate ring for Misty polynomial equations system.

        Construct all variables needed for describing Misty cryptoalgorithm
        with polynomial equations system and generate the corresponding
        Boolean Polynomial Ring.

        """
        var_names = list()

        # Input plaintext.
        var_names += self._varstrs('IN', 64)
        # Output ciphertext.
        var_names += self._varstrs('OUT', 64)

        # Key variables.
        var_names += self._varstrs('K', 128)
        # Subkey variables.
        var_names += self._varstrs('KS', 128)

        for i in range(1, self.nrounds + 1):
            var_names += self.gen_round_var_names(i)
        for i in range(1, self.nrounds + 1):
            if i % 2 == 1:
                var_names += self._varstrs('FX', 32, i)
            else:
                var_names += self._varstrs('F', 64, i)
        for i in range(self.nrounds + 1, self.nrounds + 3):
            # FL
            var_names += self._varstrs('FL_KL1', 16, i)
            var_names += self._varstrs('FL_KL2', 16, i)
            var_names += self._varstrs('FL_XOR', 16, i)
            var_names += self._varstrs('FL', 32, i)

        self.ring = BooleanPolynomialRing(len(var_names), var_names, order='degrevlex')


    def polynomials_fl(self, x, i):
        """Construct polynomials for Misty FL function."""

        left = x[:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        kl1 = self.kindex(self.KEY_KL1, i)
        kl2 = self.kindex(self.KEY_KL2, i)

        polynomials = list()

        ## Generate variables for given round
        vars_kl1 = self._vars('FL_KL1', 16, i)
        vars_kl2 = self._vars('FL_KL2', 16, i)
        vars_xor = self._vars('FL_XOR', 16, i)
        vars_out = self._vars('FL', 32, i)

        temp = vector_do(operator.__and__, left, kl1)
        polynomials.extend(vector_do(operator.__xor__, temp, vars_kl1))

        right = vector_do(operator.__xor__, right, vars_kl1)
        polynomials.extend(vector_do(operator.__xor__, right, vars_xor))

        # Replace `x or y` operation with equivalent `x * y ^ x + y`.
        temp = vector_do(operator.__or__, vars_xor, kl2)
        polynomials.extend(vector_do(operator.__xor__, temp, vars_kl2))

        left = vector_do(operator.__xor__, left, vars_kl2)
        polynomials.extend(vector_do(operator.__xor__, left, vars_out[0:16]))
        polynomials.extend(vector_do(operator.__xor__, vars_xor, vars_out[16:32]))

        return flatten(polynomials)

    def polynomials_fi(self, x, subkey_ki, subround, r):
        """Construct polynomials for Misty FI function.

        Args:
            x: list of 16 input variables.
            subkey_ki: 16-bit key chunk.
            subround: number of FI round in FO function (1..3).
            r: number of actual outer Feistel network enciphering round.

        """
        ki7 = subkey_ki[0:self.fi_right_size]
        ki9 = subkey_ki[self.fi_right_size:]

        d9 = x[0:self.fi_left_size]
        d7 = x[self.fi_left_size:]

        vars_fi = self._vars('FI' + str(subround), 16, r)
        vars_s9 = self._vars('FI' + str(subround) + '_S9', 9, r)
        vars_s7 = self._vars('FI' + str(subround) + '_S7', 7, r)
        vars_ss9 = self._vars('FI' + str(subround) + '_SS9', 9, r)
        vars_ki2 = self._vars('FI' + str(subround) + '_KI2', 9, r)

        polynomials = list()
        pad = [self.ring(0)] * 2

        polynomials.extend(self.s9(d9, vars_s9))
        d9 = vector_do(operator.__xor__, vars_s9, pad + d7) # add to pols

        polynomials.extend(self.s7(d7, vars_s7))
        d7 = vector_do(operator.__xor__, vars_s7, d9[2:self.fi_left_size]) # add to pols
        d7 = vector_do(operator.__xor__, d7, ki7)

        d9 = vector_do(operator.__xor__, d9, ki9)
        polynomials.extend(vector_do(operator.__xor__, d9, vars_ki2))

        polynomials.extend(self.s9(vars_ki2, vars_ss9))
        d9 = vector_do(operator.__xor__, vars_ss9, pad + d7) # add to pols

        polynomials.extend(vector_do(operator.__xor__, vars_fi[0:7], d7))
        polynomials.extend(vector_do(operator.__xor__, vars_fi[7:16], d9))
        return polynomials

    def polynomials_fo(self, x, i):
        """Construct polynomials for Misty FI function."""

        left = x[0:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        ki1 = self.kindex(self.KEY_KI1, i)
        ki2 = self.kindex(self.KEY_KI2, i)
        ki3 = self.kindex(self.KEY_KI3, i)

        ko1 = self.kindex(self.KEY_KO1, i)
        ko2 = self.kindex(self.KEY_KO2, i)
        ko3 = self.kindex(self.KEY_KO3, i)
        ko4 = self.kindex(self.KEY_KO4, i)

        vars_fo = self._vars('FO', 32, i)
        vars_ko1 = self._vars('FO_KO1', 16, i)
        vars_ko2 = self._vars('FO_KO2', 16, i)
        vars_ko3 = self._vars('FO_KO3', 16, i)
        vars_fi1 = self._vars('FI1', 16, i)
        vars_fi2 = self._vars('FI2', 16, i)
        vars_fi3 = self._vars('FI3', 16, i)

        polynomials = list()

        left = vector_do(operator.__xor__, left, ko1)
        polynomials.extend(vector_do(operator.__xor__, left, vars_ko1))
        polynomials.extend(self.polynomials_fi(vars_ko1, ki1, 1, i))  # FI1 variables introduced.
        left = vector_do(operator.__xor__, vars_fi1, right)

        right = vector_do(operator.__xor__, right, ko2)
        polynomials.extend(vector_do(operator.__xor__, right, vars_ko2))
        polynomials.extend(self.polynomials_fi(vars_ko2, ki2, 2, i))  # FI2 variables introduced.
        right = vector_do(operator.__xor__, vars_fi2, left)

        left = vector_do(operator.__xor__, left, ko3)
        polynomials.extend(vector_do(operator.__xor__, left, vars_ko3))
        polynomials.extend(self.polynomials_fi(vars_ko3, ki3, 3, i))  # FI3 variables introduced.
        left = vector_do(operator.__xor__, vars_fi3, right)

        right = vector_do(operator.__xor__, right, ko4)
        polynomials.extend(vector_do(operator.__xor__, right, vars_fo[0:16]))
        polynomials.extend(vector_do(operator.__xor__, left, vars_fo[16:32]))

        return polynomials

    def polynomials_round(self, data, i):
        """Construct polynomials for Misty Feistel single run."""
        left = data[0:self.halfblock_size]
        right = data[self.halfblock_size:]

        vars_fl1 = self._vars('FL', 32, i)
        vars_fl2 = self._vars('FL', 32, i + 1)
        vars_fo1 = self._vars('FO', 32, i)
        vars_fo2 = self._vars('FO', 32, i + 1)
        vars_fx = self._vars('FX', 32, i)
        vars_f = self._vars('F', 64, i + 1)

        polynomials = list()

        polynomials.extend(self.polynomials_fl(left, i))  # FL1 fariables introduced.
        polynomials.extend(self.polynomials_fl(right, i + 1))  # FL2 fariables introduced.

        polynomials.extend(self.polynomials_fo(vars_fl1, i))  # FO1 variables introduced.
        right = vector_do(operator.__xor__, vars_fo1, vars_fl2)
        polynomials.extend(vector_do(operator.__xor__, right, vars_fx))

        polynomials.extend(self.polynomials_fo(vars_fx, i + 1))  # FO2 variables introduced.
        left = vector_do(operator.__xor__, vars_fo2, vars_fl1)
        polynomials.extend(vector_do(operator.__xor__, left, vars_f[0:32]))
        polynomials.extend(vector_do(operator.__xor__, vars_fx, vars_f[32:64]))

        return polynomials

    def polynomial_system(self):
        """Construct polynomials system for Misty cipher."""

        plain = self._vars('IN', 64)
        self.key = split(self._vars('K', 128), 16)
        self.subkeys = split(self._vars('KS', 128), 16)

        polynomials = list()

        polynomials.extend(self.polynomials_round(plain, 1))  # R2_F variables introduced.
        for i in range(3, self.nrounds + 1, 2):
            vars_f_prev = self._vars('F', 64, i - 1)
            polynomials.extend(self.polynomials_round(vars_f_prev, i))

        vars_f = self._vars('F', 64, self.nrounds)
        vars_fl1 = self._vars('FL', 32, self.nrounds + 1)
        vars_fl2 = self._vars('FL', 32, self.nrounds + 2)
        vars_out = self._vars('OUT', 64)

        left = vars_f[0:self.halfblock_size]
        right = vars_f[self.halfblock_size:]

        polynomials.extend(self.polynomials_fl(left,  self.nrounds + 1))
        polynomials.extend(self.polynomials_fl(right,  self.nrounds + 2))
        polynomials.extend(vector_do(operator.__xor__, vars_fl1, vars_out[32:64]))
        polynomials.extend(vector_do(operator.__xor__, vars_fl2, vars_out[0:32]))
        return polynomials

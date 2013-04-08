#!/usr/bin/env sage
# -*- coding: utf-8 -*-

"""
MISTY block cipher polynomial system generator.

"""

__author__ = 'Ruslan Kiianchuk'
__email__ = 'ruslan.kiianchuk@gmail.com'
__version__ = '0.1'


class Misty:

    def __init__(self):
        self.nrounds = 8
        self.block_size = 64
        self.halfblock_size = self.block_size // 2
        self.halfblock_size_fo = self.halfblock_size // 2
        self.fi_left_size = 9
        self.fi_right_size = 7
        self.var_names = {
                'in': 'X',
                'key': 'K',
                'sum': 'S',
        }


    def fl(self, x, kl1, kl2):
        left = x[:self.halfblock_size_fo]
        right = x[self.halfblock_size_fo:]

        temp = map(lambda a, b: a & b, left, kl1)
        right = map(lambda a, b: a ^^ b, right, temp)

        temp = map(lambda a, b: a | b, right, kl2)
        left = map(lambda a, b: a ^^ b, left, temp)
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
        ki1 = ki[:self.fi_right_size]
        ki2 = ki[self.fi_right_size:]

        left = x[:self.fi_left_size]
        right = x[self.fi_left_size:]

        left = self.s9(left)
        left = map(lambda a, b: a ^^ b, left, right + [0, 0])

        temp = right; right = left; left = temp

        left = self.s7(left)
        left = map(lambda a, b: a ^^ b, left, right[:self.fi_right_size])
        left = map(lambda a, b: a ^^ b, left, ki1)
        right = map(lambda a, b: a ^^ b, right, ki2)

        temp = right; right = left; left = temp

        left = self.s9(left)
        left = map(lambda a, b: a ^^ b, left, right + [0, 0])

        temp = right; right = left; left = temp

        return left + right


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

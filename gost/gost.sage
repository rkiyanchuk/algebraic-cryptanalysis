#!/usr/bin/env sage
# coding: utf-8

"""
GOST 28147-89 cipher polynomial system generator.

AUTHOR: Ruslan Kiianchuk <zoresvit@gmail.com>
"""

from copy import deepcopy
from sage.crypto.mq.sbox import SBox
from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence

# TODO: with the next Sage release switch to new strings format style % -> {}

class Gost:
    """GOST 28147-89 cipher
    
    """

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

    def int2bits(self, num, bits):
        """Convert integer to list of bits.

        Args:
            n: Number to convert into bits (must be coercible to int).
            bits: Number of bits (in order to have fixed list length).

        Returns:
            List of number bits with respect to little endian.

        """
        num = Integer(num)
        return num.digits(base=2, padto=Integer(bits))

    def bits2int(self, num_bits):
        """Convert list of bits into integer number.

        Args:
            n: List of bits representing integer (in little endian, must be
            coersible to string number representation).

        Returns:
            Number represented by the given bit sequence.

        """
        num = ''.join([str(i) for i in reversed(num_bits)])
        return int(num, 2)

    def __init__(self, **kwargs):
        """Initialize GOST instance.

        Args:
            key_add: 'xor' or 'mod' string -- specifies key addition method.
                'mod' stands for addition modulo 2^32.
            sboxes: array of S-boxes used in cipher (redefines default ones).
            rounds: number of rounds during encryption (default is 32).
            block_size: cipher block bit size (default is 64).
            key_order: `frwrev` or `frw` -- order of encryption subkeys. By
                default the last 8 encryption cycles use subkeys in reversed 
                order.
            prefix: symbols to prepend the variable names with. Needed for
            building few separate systems with different plaintext/ciphertext
            values.

        """
        self.SBOX_SIZE = 4
        self.nrounds = kwargs.get('rounds', 32)
        if self.nrounds < 8:
            self.key_length = self.nrounds
        else:
            if self.nrounds % 8 != 0:
                # this limitation should be removed by separate implementation
                # of decrypt() function.
                raise ValueError('For now number of rounds must be multiple of 8')
            self.key_length = 8

        self.block_size = kwargs.get('block_size', 64)
        if self.block_size % self.SBOX_SIZE != 0 or self.block_size < 8:
            raise ValueError('Block size must be multiple of 4 (due to SBox) and greater than 8 (due to cyclic shift)')
        self.halfblock_size = self.block_size / 2

        self.key_order = kwargs.get('key_order', 'frwrev')
        if self.key_order not in ['frw', 'frwrev']:
            raise ValueError('Unsupported key ordering')
        if self.key_order is 'frwrev' and self.nrounds % 8 != 0:
            raise ValueError('frwrev key ordering is only possible for nrounds to be multiple of 8')
        self.key_add = kwargs.get('key_add', 'mod') # set key addition mode
        if self.key_add not in ['mod', 'xor']:
            raise ValueError('key_add may be set to `mod` or `xor`')

        # initialize s-box layer (if None provided, set to default GOST S-boxes)
        self._init_sboxes(kwargs.get('sboxes', None))
        pre = kwargs.get('prefix', '')
        self.var_names = {'key': 'K', 
                'block': pre + 'X', 
                'sum': pre + 'Y',
                'sbox': pre + 'Z'}
        self.gen_ring() # needed for encryption routine, not only for polynomials generation.

    def _init_sboxes(self, sboxes):
        """Generate GOST S-boxes.

        The S-boxes are converted to Sage's mq.SBox objects.

        Args:
            sboxes: List of S-boxes which are represented by a substitution
                list. If None, GOST S-boxes are initialized by the values given
                specified in GOST R 34.11-94.

        Raises:
            TypeError: Wrong S-box size or not enough S-boxes provided.

        """
        self._default_sboxes = [
                [4, 10, 9, 2, 13, 8, 0, 14, 6, 11, 1, 12, 7, 15, 5, 3],
                [14, 11, 4, 12, 6, 13, 15, 10, 2, 3, 8, 1, 0, 7, 5, 9],
                [5, 8, 1, 13, 10, 3, 4, 2, 14, 15, 12, 7, 6, 0, 9, 11],
                [7, 13, 10, 1, 0, 8, 9, 15, 14, 4, 6, 12, 11, 2, 5, 3],
                [6, 12, 7, 1, 5, 15, 13, 8, 4, 10, 9, 14, 0, 3, 11, 2],
                [4, 11, 10, 0, 7, 2, 1, 13, 3, 6, 8, 5, 9, 12, 15, 14],
                [13, 11, 4, 1, 3, 15, 5, 9, 0, 10, 14, 7, 6, 8, 2, 12],
                [1, 15, 13, 0, 5, 7, 10, 4, 9, 2, 3, 14, 6, 11, 8, 12]
                ]
        if not sboxes:
            sboxes = self._default_sboxes
        else:
            # check for correct input
            for s in sboxes:
                if len(s) != 2 ^ self.SBOX_SIZE: 
                    raise TypeError('S-box must be 4x4 bits (0..15)')
        self.sboxes = [SBox(i, big_endian=False) for i in sboxes]

    def gen_ring(self):
        """Return a ring which holds all variables of GOST instance."""
        nr = self.nrounds
        bs = self.block_size
        hbs = self.halfblock_size
        var_names = []
        halfblock_vars = [self.var_names['key'], self.var_names['sum'], self.var_names['sbox']]
        for r in range(nr):
            var_names += [self._varformatstr(v) % (r, b) 
                    for v in halfblock_vars for b in xrange(hbs)]
        # Final X vars after last round (corresponds to ciphertext)
        for r in range(nr + 1):
            var_names += [self._varformatstr(self.var_names['block']) % (r, b) 
                    for b in xrange(bs)]
        self.ring = BooleanPolynomialRing(len(var_names), var_names, order='degrevlex') 
        return self.ring

    def polynomial_system(self):
        """Return a polynomial system of self GOST intance.

        Returns:
            PolynomialSequence object constructed from the polynomials that
            fully describe GOST encryption. Round polynomials are stored in a
            sublist so one can get the round polynomials with
            PolynomialSequence.part(number_of_round).
        """
        hbs = self.halfblock_size
        mqsystem_parts = []

        kvars = list()
        for i in range(self.key_length):
            kvars.append(map(self.ring, self.gen_vars(self.var_names['key'], i)))

        for i in range(self.nrounds):
            xvars = map(self.ring, self.gen_vars(self.var_names['block'], i))
            yvars = map(self.ring, self.gen_vars(self.var_names['sum'], i))
            zvars = map(self.ring, self.gen_vars(self.var_names['sbox'], i))
            next_xvars = map(self.ring, self.gen_vars(self.var_names['block'], i + 1))
            polynomials = []
            
            # feed keys in reverse order if `frwrev` ordering is set
            if self.key_order == 'frwrev' and i >= (self.nrounds - self.key_length):
                k = self.key_length - 1 - (i % self.key_length)
            else:
                k = i % self.key_length
            polynomials += self.add_round_key(xvars[:hbs], kvars[k], yvars)
            # sbox layer polynomials
            polynomials += self.polynomials_sbox(yvars, zvars)
            # shift is just variables substitution
            zvars = self.shift(zvars)
            # xor halfblocks
            xored = self.xor_blocks(xvars[hbs:], zvars)
            if i < self.nrounds - 1:
                # R_{i+1} = L_i xor f(R_i)
                polynomials += [x + y for x, y in zip(xored, next_xvars[:hbs])]
                # L_{i+1} = R_i
                polynomials += [x + y for x, y in zip(xvars[:hbs], next_xvars[hbs:])]
            else:
                # No block swapping in the last round.
                # R_{i+1} = L_i
                polynomials += [x + y for x, y in zip(xvars[:hbs], next_xvars[:hbs])]
                # L_{i+1} = L_i xor f(R_i)
                polynomials += [x + y for x, y in zip(xored, next_xvars[hbs:])]
            mqsystem_parts.append(polynomials)
        return PolynomialSequence(mqsystem_parts, self.ring)

    def polynomials_sbox(self, yvars, zvars):
        """Generate polynomials describing substitution layer.

        Polynomials list describing each S-Box is generated and mapped onto
        the ring which is used for describing the cipher variables.
        
        """
        polynomials = list()
        # TODO: why need copying here?
        sboxes = deepcopy(self.sboxes)
        for i in range(self.halfblock_size / self.SBOX_SIZE):
            nbit = i * self.SBOX_SIZE
            current_sbox = sboxes[i % len(sboxes)]
            # form variables dict for subs()
            pols = current_sbox.polynomials()
            gens = current_sbox.ring().gens()
            new_gens = yvars[nbit:nbit + self.SBOX_SIZE] + zvars[nbit:nbit + self.SBOX_SIZE] 
            # substitute generators of sbox polynomials with GOST ring gens
            sub = dict(zip(gens, new_gens))
            pols = [p.subs(sub) for p in pols]
            polynomials += pols
        return polynomials

    def __repr__(self):
        """Return string describing GOST instance."""
        gost_id = 'GOST cipher '
        gost_id += '(Block Size = %d, Rounds = %d, '
        gost_id += 'Key Addition = %s, Key Order = %s)' 
        params = (self.block_size, self.nrounds, self.key_add, self.key_order)
        return gost_id % params

    def add_round_key(self, a, b, r=[]):
        """Inject subkey into data.

        Depending on the `key_add` option the key is either added modulo 2^32 or
        xored with the halfblock data.

        """
        hbs = self.halfblock_size
        is_defined  = lambda vals: all([p.constant() for p in vals])
        # If all variables are defined, just compute the result instead of
        # generating polynomials.
        if is_defined(a) and is_defined(b):
            if self.key_add is 'mod':
                data = self.bits2int(a)
                subkey = self.bits2int(b)
                modulo_mask = (1 << hbs) - 1
                result = (data + subkey) & modulo_mask
                return [self.ring(i) for i in self.int2bits(result, hbs)]
            if self.key_add is 'xor':
                return [x + y for x, y, in zip(a, b)]    
        else:
            if self.key_add is 'mod':
                pols = list()
                pols.append(a[0] + b[0] + r[0]) # TODO: this polynomial is most likely redundant and linearly dependent
                for i in range(0, hbs - 1):
                    pols.append(a[i] + a[i] * r[i] + a[i] * r[i+1] + a[i] *
                            a[i+1] + a[i] * b[i+1] + r[i] * r[i+1] + r[i] *
                            a[i+1] + r[i] * b[i+1])
                    pols.append(b[i] + b[i] * r[i] + b[i] * r[i+1] + b[i] *
                            a[i+1] + b[i] * b[i+1] + r[i] * r[i+1] + r[i] *
                            a[i+1] + r[i] * b[i+1])
                    pols.append(a[i] * r[i] + b[i] * r[i] + a[i] * b[i] + a[i]
                            + b[i] + r[i+1] + a[i+1] + b[i+1])
                return pols
            if self.key_add is 'xor':
                return [x + y + z for x, y, z in zip(r, a, b)]    

    def shift(self, halfblock):
        """Perform cyclic shift of halfblock data by 11 bits to the left (if the
        bit sequence is presented in big endian).

        This function is assuming the input halfblock is in little endian so it
        actually performs right cyclic shift. 

        """
        # 11-bit shift value in GOST specification is rounded third part of
        # halfblock size. Scale shift values for smaller block sizes.
        shift = ceil(self.halfblock_size / 3)
        halfblock = halfblock[self.halfblock_size-shift:self.halfblock_size] + halfblock[0:self.halfblock_size-shift]
        return halfblock

    def substitute(self, halfblock):
        """Substitue every 4 bits of input halfblock by the corresponding
        S-box value.

        """
        result = []
        for i in range(self.halfblock_size / self.SBOX_SIZE):
            nbit = i * self.SBOX_SIZE
            plain = halfblock[nbit:nbit + self.SBOX_SIZE]
            sub = self.sboxes[i % len(self.sboxes)](plain)
            sub = [self.ring(j) for j in sub]
            result += sub
        return result

    def xor_blocks(self, left, right):
        """XOR blocks of data devined over BooleanPolynomialRing."""
        return [x + y for x, y in zip(left, right)]

    def feistel_round(self, block, subkey):
        """Perform one round of Feistel structure.

        Args:
            block: data for encryption. Represented by list of bits.
            subkey: round encryption key. Represented by an integer.

        Returns:
            data block encrypted by a single GOST round.

        """
        hbs = self.halfblock_size
        bs = self.block_size
        n1 = block[0:hbs] # left
        n2 = block[hbs:bs]; # right
        temp = n1
        n1 = self.add_round_key(n1, subkey)
        n1 = self.substitute(n1);
        n1 = self.shift(n1);
        n2 = self.xor_blocks(n1, n2)
        n1 = temp
        return n2 + n1

    def _cast_params(self, data_, key_):
        # avoid changing input parameters
        bs = self.block_size
        data = deepcopy(data_)
        key = deepcopy(key_)
        # coerse input data to ring elements
        if not isinstance(data, list):
            data = self.int2bits(data, bs)
        data = [self.ring(i) for i in data]
        if len(key) != self.key_length:
            raise TypeError('Key should be of length ' + str(self.key_length))
        # coerse key bits to ring elements
        for i in range(len(key)):
            if not isinstance(key[i], list):
                key[i] = self.int2bits(key[i], self.halfblock_size)
            key[i] = [self.ring(j) for j in key[i]]
        return data, key

    def encrypt(self, data_, key_):
        """Encrypt input data block with the specified key.

        If key_order = 'frwrev', then during the last 8 rounds the keys will be
        fed in reverse order.

        """
        hbs = self.halfblock_size
        bs = self.block_size
        data, key = self._cast_params(data_, key_)

        for i in range(self.nrounds):
            # feed keys in reverse order if `frwrev` ordering is set
            if self.key_order == 'frwrev' and i >= (self.nrounds - self.key_length):
                k = self.key_length - 1 - (i % self.key_length)
            else:
                k = i % self.key_length
            data = self.feistel_round(data, key[k])
        # cancel block swapping in the last round
        data = data[hbs:bs] + data[0:hbs]
        return self.bits2int(data)

    def decrypt(self, data_, key_):
        """Decrypt input data block with the specified key.

        If key_order = 'frwrev', then during the last 8 rounds the keys will be
        fed in reverse order.

        """
        hbs = self.halfblock_size
        bs = self.block_size
        data, key = self._cast_params(data_, key_)

        key.reverse()
        for i in range(self.nrounds):
            # feed keys in reverse order if `frwrev` ordering is set
            if self.key_order == 'frwrev' and i < self.key_length:
                k = self.key_length - 1 - (i % self.key_length)
            else:
                k = i % self.key_length
            data = self.feistel_round(data, key[k])
        # cancel block swapping in the last round
        data = data[hbs:bs] + data[0:hbs]
        return self.bits2int(data)

    def random_key(self):
        key = [list(random_vector(int(self.halfblock_size), x=2)) 
                for _ in range(self.key_length)]
        key = [map(self.ring, i) for i in key]
        return key

    def random_block(self):
        return map(self.ring, list(random_vector(self.block_size, x=2)))

    def test_mqsystem(self, f_):
        if f_.ring() is not self.ring:
            raise TypeError('Tested MQ system has been generated by a ' 
                    'different GOST instance')
        f = copy(f_)
        print 'Testing MQ system', f
        bs = self.block_size
        plaintext = self.random_block()
        key = self.random_key()
        ciphertext = self.int2bits(self.encrypt(plaintext, key), bs)

        f = f.subs(dict(zip(self.gen_vars(self.var_names['block'], 0), plaintext)))
        f = f.subs(dict(zip(self.gen_vars(self.var_names['block'], self.nrounds), ciphertext)))
        for i in range(self.nrounds):
            # feed keys in reverse order if `frwrev` ordering is set
            k = i % self.key_length
            f = f.subs(dict(zip(self.gen_vars(self.var_names['key'], i), key[k])))
        s = f.ideal().interreduced_basis()
        if s == [1]:
            print 'MQ System for' + str(self) + 'is INCORRECT'
            print f
            return False
        else:
            return True


    def test_cipher(self):
        """Test GOST 28147-89 cipher for correct encryption.

        The test includes several keys and plaintexts with expected ciphertext
        values. 

        Returns:
            True: If all tests have been passed.
            False: If any of the test failed. Values of the key, plaintext, 
                actual and expected ciphertext values are shown on test case 
                failure.

        """
        # testing data
        keys = [
                [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0], 
                [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], 
                [0x01234567, 0x89ABCDEF, 0x01234567, 0x89ABCDEF, 0x01234567, 0x89ABCDEF, 0x01234567, 0x89ABCDEF], 
                [0x6ebabf8d, 0x1a8cad60, 0x124744f9, 0xd400b5d8, 0xa721e3fd, 0x11d0702d, 0x06fd4827, 0x476df4bf]
                ]
        plain = [
                0x0000000000000000, 0xBDBDBDBDACACACAC, 0xFFFFFFFFFFFFFFFF, 0x89ABCDEF01234567, 0xC0AE942BC8A99A39
                ]
        cipher = [
                0x12610BE2A6C2FDC9, 0xA587E5D3F6DFB6F4, 0x029BFE67A9364E44, 0x523FC1A6AEC71B9A, 0x780CB7CE063F59E2,
                0x9057C2CF13AAAD6D, 0xF7B085BA4771F406, 0x780416781B29BC06, 0xE596A183FD645558, 0x8EC42736538740AB,
                0xF1956B1D0A1A67DE, 0x9E4C808408DCDBDC, 0x7738AF92DE8FC770, 0x9C44633FCEC0A03E, 0xC23013406002E268,
                0x91DB8E1FE489FAEF, 0x547BF353604A8190, 0x92B517E3CC91B9D0, 0x1F5C2195762513E2, 0xE99D1C8DFF44A74C
                ]

        def show_failed(plain, key, result, expected):
            print 'GOST FAILED'
            print 'key:\t\t', ['0x%8.8X' % subk for subk in key]
            print 'plaintext:\t', "0x%16.16X" % plain
            print 'expected:\t', "0x%16.16X" % expected
            print 'actual:\t\t', "0x%16.16X" % result

        if self.block_size == 64 and self.nrounds == 32 and self.key_add == 'mod' and self.key_order == 'frwrev':
            print 'Testing ', self, 'using test vectors...'
            it = cipher.__iter__()
            for k in keys:
                for p in plain:
                    c = self.encrypt(p, k)
                    expected = it.next() 
                    if c != expected:
                        show_failed(p, k, c, expected)
                        return False
        print 'Testing', self, 'by correct decryption...'
        x = randint(0, 2^self.block_size)
        key = list(random_vector(self.key_length, x = 2^self.block_size))
        c = self.encrypt(x, key)
        d = self.decrypt(c, key)
        if x != d:
            show_failed(x, key, d, x)
            return False
        return True

# AFAIK, Sage always set's name to __main__ when loading/attaching file.
# if __name__ == "__main__":
if False:
    g = Gost(block_size=64, rounds=4, key_add='xor', key_order='frw')
    print g.test_cipher()
    print 'Generating polynomial system...'
    f = g.polynomial_system()
    print g.test_mqsystem(f)
    print ''

    g = Gost(block_size=64, rounds=8, key_add='mod', key_order='frw')
    print g.test_cipher()
    print 'Generating polynomial system...'
    f = g.polynomial_system()
    print g.test_mqsystem(f)
    print ''

    g = Gost(block_size=64, rounds=32, key_add='mod', key_order='frwrev')
    print g.test_cipher()
    print 'Generating polynomial system...'
    f = g.polynomial_system()
    print g.test_mqsystem(f)
    print ''

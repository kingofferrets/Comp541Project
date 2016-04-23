import itertools
from array import array
from string import join
from struct import pack
import random


class EquationContext:
    """
    A class used to generate a single SAT formula.

    This class keeps track of all generated variables and clauses.
    """
    def __init__(self):
        self.var_id = 0
        self.clauses = []
        self.clause_id = 0

        self.t = self.fresh_variable()
        self.cnf_clause(self.t)

    def fresh_variable(self):
        self.var_id += 1
        return self.var_id

    def fresh_variables(self, N):
        return [self.fresh_variable() for _ in xrange(N)]

    def true(self):
        return self.t

    def false(self):
        return -1 * self.t

    def cnf_clause(self, *variables):
        self.clause_id += 1
        self.clauses.append(('', variables))

    def xor_clause(self, *variables):
        self.clause_id += 1
        self.clauses.append(('x', variables))

    def comment(self, comment_str):
        self.clauses.append(('c', comment_str))

    def write(self, fname):
        f = open(fname, 'w')

        f.write('p cnf ' + str(self.var_id) + ' ' + str(self.clause_id) + '\n')
        for clause in self.clauses:
            if clause[0] == 'c':
                f.write('c ' + str(clause[1]) + '\n')
            else:
                f.write(str(clause[0]) + ' '.join(map(str, clause[1])) + ' 0\n')
        f.close()


# Each helper function here encodes a single computation of the MD4 hash function
def compute_not(eqn, X):
    return [-1 * x for x in X]


def compute_or(eqn, X, Y):
    res = eqn.fresh_variables(32)
    for i in xrange(32):
        eqn.cnf_clause(-1 * res[i], X[i], Y[i])
        eqn.cnf_clause(res[i], -1 * X[i])
        eqn.cnf_clause(res[i], -1 * Y[i])


def compute_and(eqn, X, Y):
    nX = compute_not(eqn, X)
    nY = compute_not(eqn, Y)

    return compute_not(eqn, compute_or(eqn, nX, nY))


def compute_f(eqn, X, Y, Z):
    # f(X,Y,Z)  =  XY v not(X)Z
    res = eqn.fresh_variables(32)
    for i in xrange(32):
        eqn.cnf_clause(-1 * res[i], X[i], Z[i])
        eqn.cnf_clause(-1 * res[i], -1 * X[i], Y[i])
        eqn.cnf_clause(-1 * res[i], Y[i], Z[i])
        eqn.cnf_clause(res[i], -1 * X[i], -1 * Y[i])
        eqn.cnf_clause(res[i], X[i], -1 * Z[i])
    return res


def compute_g_step(eqn, x, y, z, res):
    # res = xy v xz v yz
    eqn.cnf_clause(-1 * res, x, y)
    eqn.cnf_clause(-1 * res, x, z)
    eqn.cnf_clause(-1 * res, y, z)
    eqn.cnf_clause(res, -1 * x, -1 * y)
    eqn.cnf_clause(res, -1 * x, -1 * z)
    eqn.cnf_clause(res, -1 * y, -1 * z)


def compute_g(eqn, X, Y, Z):
    # g(X,Y,Z)  =  XY v XZ v YZ
    res = eqn.fresh_variables(32)
    for i in xrange(32):
        compute_g_step(eqn, X[i], Y[i], Z[i], res[i])
    return res


def compute_h(eqn, X, Y, Z):
    # h(X,Y,Z)  =  X xor Y xor Z
    h = eqn.fresh_variables(32)
    for i in xrange(32):
        eqn.xor_clause(-1 * h[i], X[i], Y[i], Z[i])
    return h


def add(eqn, X, Y):
    # res = (X + Y) % 2^32

    # Note low order bits appear first in each

    carry = [eqn.false()] + eqn.fresh_variables(31)  # the first carry bit is always false
    for i in xrange(31):  # drop the last carry bit
        # carry[i+1] == (at least two of X[i], Y[i], and carry[i] are true)
        compute_g_step(eqn, X[i], Y[i], carry[i], carry[i+1])

    # result[i] = X[i] xor Y[i] xor carry[i]
    return compute_h(eqn, X, Y, carry)


def rot(eqn, X, s):
    # rotate X left s bits
    #  i.e. make lowest order bit higher by s
    return X[-s:] + X[:-s]


def from_constant(eqn, constant):
    # Note LOW order bits are first in result

    res = []
    for i in xrange(32):
        if constant % 2 == 0:
            res.append(eqn.false())
        else:
            res.append(eqn.true())
        constant = int(constant / 2)
    return res


def round_1(eqn, A, B, C, D, i, s, msg):
    comp_f = compute_f(eqn, B, C, D)
    sum_1 = add(eqn, A, comp_f)
    sum_2 = add(eqn, sum_1, msg[i])
    return rot(eqn, sum_2, s)


def round_2(eqn, A, B, C, D, i, s, msg, round_2_constant):
    comp_g = compute_g(eqn, B, C, D)
    sum_1 = add(eqn, A, comp_g)
    sum_2 = add(eqn, msg[i], round_2_constant)

    return rot(eqn, add(eqn, sum_1, sum_2), s)


def round_3(eqn, A, B, C, D, i, s, msg, round_3_constant):
    comp_h = compute_h(eqn, B, C, D)
    sum_1 = add(eqn, A, comp_h)
    sum_2 = add(eqn, msg[i], round_3_constant)

    return rot(eqn, add(eqn, sum_1, sum_2), s)


def generate_md4(rounds, steps):
    """
    Generate an equation representing an md4 hash

    :param rounds: The number of rounds to perform (0-3)
    :param steps: The number of steps to perform (0-16)
    :return: [variables for input], [variables for output], equation
    """

    eqn = EquationContext()

    # The message is a 16-word block w/ 32 bits per word
    msg = [eqn.fresh_variables(32) for _ in xrange(16)]

    Q = []
    Q.append(from_constant(eqn, 0x67452301))  # A
    Q.append(from_constant(eqn, 0x10325476))  # D
    Q.append(from_constant(eqn, 0x98badcfe))  # C
    Q.append(from_constant(eqn, 0xefcdab89))  # B

    if rounds > 0:
        round_1_rot = [3, 7, 11, 19] * 4
        round_1_index = range(16)

        for i in xrange(steps):
            Q.append(round_1(eqn, Q[-4], Q[-1], Q[-2], Q[-3], round_1_index[i], round_1_rot[i], msg))

    if rounds > 1:
        # Perform the 2nd round
        round_2_rot = [3, 5, 9, 13] * 4
        round_2_index = [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
        round_2_constant = from_constant(eqn, 0x5a827999)

        for i in xrange(steps):
            Q.append(round_2(eqn, Q[-4], Q[-1], Q[-2], Q[-3], round_2_index[i], round_2_rot[i], msg, round_2_constant))

    if rounds > 2:
        # Perform the 3rd round
        round_3_rot = [3, 9, 11, 15] * 4
        round_3_index = [0, 8, 4, 12, 2, 10, 6, 14,  1, 9, 5, 13, 3, 11, 7, 15]
        round_3_constant = from_constant(eqn, 0x6ed9eba1)

        for i in xrange(steps):
            Q.append(round_3(eqn, Q[-4], Q[-1], Q[-2], Q[-3], round_3_index[i], round_3_rot[i], msg, round_3_constant))

    A = add(eqn, Q[0], Q[-4])
    B = add(eqn, Q[3], Q[-1])
    C = add(eqn, Q[2], Q[-2])
    D = add(eqn, Q[1], Q[-3])

    # Compute the 128 variables which form the result
    result = A + B + C + D

    # Compute the 512 variables which form the input
    original_input = list(itertools.chain(*msg))

    return original_input, result, eqn


def generate_benchmark_forwards(message, rounds, steps, fname):
    """
    Generate an MD4 benchmark to compute the MD4 of a given input

    :param binary_hash: The hash to invert
    :param rounds: The number of round of MD4 to use
    :param steps: The number of steps per round of MD4
    :param fname: File to output the final formula to
    :return: None
    """
    msg, result, eqn = generate_md4(rounds, steps)

    message = str(message)

    bits = msg_to_bits(message)

    for bit, var in zip(bits, msg):
        if bit == '1':
            eqn.cnf_clause(var)
        else:
            eqn.cnf_clause(-1 * var)

    eqn.comment('Rounds: ' + str(rounds))
    eqn.comment('Steps: ' + str(steps))
    eqn.comment('Input: ' + message)
    real = md4_actual(message, rounds, steps)
    eqn.comment('Expected hash: ' + str(real))
    eqn.comment('Key variables: ' + str(result))
    real_bits = hash_bits_from_hex(real)

    real_result = []
    for bit, var in zip(real_bits, result):
        if bit == '1':
            real_result.append(var)
        else:
            real_result.append(-var)
    eqn.comment('Expected result: ' + str(real_result))

    fname = 'xor/' + fname
    eqn.write(fname)
    return 'Output at ' + fname


def generate_benchmark_backwards(binary_hash, rounds, steps, fname):
    """
    Generate an MD4 benchmark to invert a given hash

    :param binary_hash: The hash to invert
    :param rounds: The number of round of MD4 to use
    :param steps: The number of steps per round of MD4
    :param fname: File to output the final formula to
    :return: None
    """
    msg, result, eqn = generate_md4(rounds, steps)

    if len(binary_hash) != 128:
        raise ValueError('binary_hash must be a 128-digit string of 0 and 1')

    # Set the size of the hash to find to be 448 bits
    size_bits = '0001110110000000000000000000000000000000000000000000000000000000'
    for var, bit in zip(msg[448:], size_bits):
        if bit == '1':
            eqn.cnf_clause(var)
        else:
            eqn.cnf_clause(-1 * var)

    for var, bit in zip(result, binary_hash):
        if bit == '1':
            eqn.cnf_clause(var)
        else:
            eqn.cnf_clause(-1 * var)

    eqn.comment('Rounds: ' + str(rounds))
    eqn.comment('Steps: ' + str(steps))
    eqn.comment('Desired Hash (hex): ' + hex_from_hash_bits(binary_hash))
    eqn.comment('Desired Hash (bin): ' + binary_hash)
    eqn.comment('Input Vars: ' + str(msg[:448]))

    fname = 'xor/' + fname
    eqn.write(fname)
    return 'Output at ' + fname


def generate_md4_official_benchmarks(num_to_generate=100):
    """
    Generate a series of benchmarks for 3-round 7-step MD4

    :param num_to_generate: The number of benchmarks to generate
    :return: None
    """
    rounds = 3
    steps = 7

    random.seed(31337)  # Ensure we always generate the same benchmarks

    for i in xrange(num_to_generate):
        goal_bits = ''.join([random.choice(['0', '1']) for _ in xrange(128)])

        goal_hash = hex_from_hash_bits(goal_bits)
        fname = "{0}-{1}-{2}{3}.cnf".format(i, goal_hash, rounds, steps)
        generate_benchmark_backwards(goal_bits, rounds, steps, fname)


# Working implementation of MD4 follows below, used to test correctness of the generated SAT formulas
# The code below is adapted from https://gist.github.com/tristanwietsma/5937448
_DECODE = lambda x, e: list(array('B', x.decode(e)))
_ENCODE = lambda x, e: join([chr(i) for i in x], '').encode(e)
HEX_TO_BYTES = lambda x: _DECODE(x, 'hex')
TXT_TO_BYTES = lambda x: HEX_TO_BYTES(x.encode('hex'))
BYTES_TO_HEX = lambda x: _ENCODE(x, 'hex')
BYTES_TO_TXT = lambda x: BYTES_TO_HEX(x).decode('hex')


def _working_pad(msg):
    n = len(msg)
    bit_len = n * 8
    index = (bit_len >> 3) & 0x3fL
    pad_len = 120 - index
    if index < 56:
        pad_len = 56 - index
    padding = '\x80' + '\x00'*63
    padded_msg = msg + padding[:pad_len] + pack('<Q', bit_len)
    return padded_msg


def _left_rotate(n, b):
    return ((n << b) | ((n & 0xffffffff) >> (32 - b))) & 0xffffffff


def _f(x, y, z): 
    return x & y | ~x & z


def _g(x, y, z): 
    return x & y | x & z | y & z


def _h(x, y, z): 
    return x ^ y ^ z


def _f1(a, b, c, d, k, s, X):
    return _left_rotate(a + _f(b, c, d) + X[k], s)


def _f2(a, b, c, d, k, s, X, round_2_constant):
    return _left_rotate(a + _g(b, c, d) + X[k] + round_2_constant, s)


def _f3(a, b, c, d, k, s, X, round_3_constant):
    return _left_rotate(a + _h(b, c, d) + X[k] + round_3_constant, s)


def get_binary(num, digits):
    res = ''
    for _ in xrange(digits):
        if num % 2 == 1:
            res += '1'
        else:
            res += '0'
        num = int(num / 2)
    return res


def msg_to_bits(message_string):
    msg_bytes = TXT_TO_BYTES(_working_pad(message_string))
    block = msg_bytes[0:64]

    return ''.join([get_binary(n, 8) for n in block])


def num_from_bits(bits):
    res = 0
    place = 1
    for b in bits:
        if b == '1':
            res += place
        place *= 2
    return res


def hex_from_hash_bits(bits):
    lookup = {get_binary(int(i, 16), 4): i for i in
              ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']}

    letters = [lookup[bits[i+4:i+8]] + lookup[bits[i:i+4]] for i in xrange(0, len(bits), 8)]
    return ''.join(letters)


def hash_bits_from_hex(hex):
    lookup = {i: get_binary(int(i, 16), 4) for i in
              ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']}

    bits = [lookup[hex[i+1]] + lookup[hex[i]] for i in xrange(0, len(hex), 2)]
    return ''.join(bits)


def md4_actual(message_string, rounds, steps, message_in_bits=False):
    if message_in_bits:
        bits = message_string
        if len(bits) < 448:
            bits += '0' * (448 - len(bits))
        if len(bits) > 448:
            raise ValueError('Unable to hash things above 448 bits; I removed that functionality')
        bits += '0001110110000000000000000000000000000000000000000000000000000000'
    else:
        bits = msg_to_bits(message_string)

    msg = [num_from_bits(bits[i:i+32]) for i in xrange(0, 512, 32)]

    Q = []
    Q.append(0x67452301)  # A
    Q.append(0x10325476)  # D
    Q.append(0x98badcfe)  # C
    Q.append(0xefcdab89)  # B

    round_1_rot = [3, 7, 11, 19] * 4
    round_1_index = range(16)

    for i in xrange(steps):
        Q.append(_f1(Q[-4], Q[-1], Q[-2], Q[-3], round_1_index[i], round_1_rot[i], msg))

    if rounds > 1:
        # Perform the 2nd round
        round_2_rot = [3, 5, 9, 13] * 4
        round_2_index = [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
        round_2_constant = 0x5a827999

        for i in xrange(steps):
            Q.append(_f2(Q[-4], Q[-1], Q[-2], Q[-3], round_2_index[i], round_2_rot[i], msg, round_2_constant))

    if rounds > 2:
        # Perform the 3rd round
        round_3_rot = [3, 9, 11, 15] * 4
        round_3_index = [0, 8, 4, 12, 2, 10, 6, 14,  1, 9, 5, 13, 3, 11, 7, 15]
        round_3_constant = 0x6ed9eba1

        for i in xrange(steps):
            Q.append(_f3(Q[-4], Q[-1], Q[-2], Q[-3], round_3_index[i], round_3_rot[i], msg, round_3_constant))

    # update state
    A = (Q[0] + Q[-4]) & 0xffffffff
    B = (Q[3] + Q[-1]) & 0xffffffff
    C = (Q[2] + Q[-2]) & 0xffffffff
    D = (Q[1] + Q[-3]) & 0xffffffff

    return hex_from_hash_bits(get_binary(A, 32) + get_binary(B, 32) + get_binary(C, 32) + get_binary(D, 32))


if __name__ == '__main__':
    def Check(msg, sig):
        res = md4_actual(msg, 3, 16)
        print res == sig

    Check("", '31d6cfe0d16ae931b73c59d7e0c089c0')
    Check("a", 'bde52cb31de33e46245e05fbdbd6fb24')
    Check("abc", 'a448017aaf21d8525fc10ae87aa6729d')
    Check("message digest", 'd9130a8164549fe818874806e1c7014b')
    Check("abcdefghijklmnopqrstuvwxyz", 'd79e1c308aa5bbcdeea8ed63df412da9')
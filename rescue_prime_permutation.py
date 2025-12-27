import math
from sage.all import matrix, vector, ZZ, GCD, binomial, FiniteField
from Crypto.Hash import SHAKE256
from Crypto.Util.number import inverse


# Rescue Prime permutation function
def rescue_permute(m, state, field, rounds, constants, alpha, alpha_inv, MDS):
    for i in range(rounds):
        # each element raised to the power of alpha
        for j in range(m):
            state[j] = pow(state[j], alpha)

        # Linear Layer
        state = list(MDS * vector(state))

        # inject round constants
        for j in range(m):
            state[j] = field(state[j] + constants[2*i*m+j])

        # each element raised to the power of alpha_inverse
        for j in range(m):
            state[j] = pow(state[j], alpha_inv)

        # Linear Layer
        state = list(MDS * vector(state))

        # inject round constants
        for j in range(m):
            state[j] = field(state[j] + constants[2*i*m+m+j])

    # output final state
    for i in range(len(state)):
        print(hex(state[i]))


# generate round constants
def gen_round_constants(security_bits, p, m, c, N, field):
    assert security_bits == 128 or security_bits == 160

    # generate pseudorandom bytes using SHAKE256
    shake256 = SHAKE256.new()
    bytes_per_int = math.ceil(len(bin(p)[2:]) / 8) + 1 # generate slightly larger then reduce mod p
    seed_string = f"Rescue-XLIX({p},{m},{c},{security_bits})"
    shake256.update(bytes(seed_string, "ascii"))

    constants = []
    for _ in range(2*m*N): # 2 round constants per state element per round
        chunk = shake256.read(bytes_per_int)
        temp = sum(256**j * ZZ(chunk[j]) for j in range(len(chunk))) # base 256 expansion, multiply using ZZ into place
        constants.append(field(temp % p))

    assert len(constants) == 2*m*N # make sure we have the required number of constants for 2 injections per round

    print(constants)
    return constants


# generate MDS matrix
def gen_mds_matrix(p, m, field):
    # find a generator
    #g = field.multiplicative_generator()
    g = field(7)
    V = matrix([[g**(i*j) for j in range(2*m)] for i in range(m)])
    V_ech = V.echelon_form()

    return V_ech[:, m:].transpose()


# get number of rounds needed
def get_number_of_rounds(p, m, capacity, security_level, alpha):
    rate = m - capacity
    dcon = lambda N : math.floor(0.5 * (alpha - 1) * m * (N - 1) + 2)
    v = lambda N : m *(N - 1) + rate
    target = 2**security_level

    temp = 0
    for i in range(1, 25):
        if binomial(v(i) + dcon(i), v(i))**2 > target:
            temp = i
            break

    return math.ceil(1.5 * max(5, temp))


# print the MDS matrix for use in Halo2 circuit
def print_mds(MDS, m):
    for i in range(m):
        col = MDS.column(i)
        print(f"Column: {i}")
        for j in range(m):
            print(f"\t{hex(int(col[j]))}")


# main function
def main():
    c = 1
    r = 2
    m = c + r
    p = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
    security_level = 128
    field = FiniteField(p)
    alpha = 5
    alpha_inv = inverse(alpha, p-1)
    print(f"[*] alpha_inv: {alpha_inv}")
    assert GCD(alpha, p-1) == 1

    # parameter generation
    rounds = get_number_of_rounds(p, m, c, security_level, alpha)
    print(f"Rounds: {rounds}")
    bls12381_rcs = gen_round_constants(security_level, p, m, c, rounds, field)
    MDS = gen_mds_matrix(p, m, field)
    print_mds(MDS, m)

    # convert all round constants to field elements
    bls12381_rcs = [field(x) for x in bls12381_rcs]

    # running the permutation
    init_state = [field(0), field(1), field(2)]
    
    rescue_permute(m, init_state, field, rounds, bls12381_rcs, alpha, alpha_inv, MDS)


if __name__ == '__main__':
    main()
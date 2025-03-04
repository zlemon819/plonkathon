from utils import *
import py_ecc.bn128 as b
from curve import ec_lincomb, G1Point, G2Point
from compiler.program import CommonPreprocessedInput
from verifier import VerificationKey
from dataclasses import dataclass
from poly import Polynomial, Basis

# Recover the trusted setup from a file in the format used in
# https://github.com/iden3/snarkjs#7-prepare-phase-2
SETUP_FILE_G1_STARTPOS = 80
SETUP_FILE_POWERS_POS = 60


@dataclass
class Setup(object):
    #   ([1]₁, [x]₁, ..., [x^{d-1}]₁)
    # = ( G,    xG,  ...,  x^{d-1}G ), where G is a generator of G_1
    powers_of_x: list[G1Point] 
    # [x]₂ = xH, where H is a generator of G_2
    X2: G2Point

    @classmethod
    def from_file(cls, filename):
        # open a file in binary read(“rb”) model 
        contents = open(filename, "rb").read() 
        # Byte 60 gives you the base-2 log of how many powers there are
        powers = 2 ** contents[SETUP_FILE_POWERS_POS]
        # there are 2048 points for the setup 
        print(powers);

        # Extract G1 points, which start at byte 80
        # step in "for i in range" be 32, it store both x, y coordinates for each 32 bytes.
        values = [
            int.from_bytes(contents[i : i + 32], "little")
            for i in range(
                SETUP_FILE_G1_STARTPOS, SETUP_FILE_G1_STARTPOS + 32 * powers * 2, 32
            )
        ]
        # the length of values is 4096
        print(len(values));
        assert max(values) < b.field_modulus
        # b.field_modulus = 21888242871839275222246405745257275088696311157297823662689037894645226208583
        # means this library use bn128 curve
        print(b.field_modulus);

        # The points are encoded in a weird encoding, where all x and y points
        # are multiplied by a factor (for montgomery optimization?). We can
        # extract the factor because we know the first point is the generator.

        # # Generator for curve over FQ(a class for field element): G1 = (FQ(1), FQ(2))
        print(type(values[0]));
        factor = b.FQ(values[0]) / b.G1[0]

        # get the actual x, y coordinates after diving by the factor
        values = [b.FQ(x) / factor for x in values]
        
        powers_of_x = [(values[i * 2], values[i * 2 + 1]) for i in range(powers)]
        print("Extracted G1 side, X^1 point: {}".format(powers_of_x[1]))
        print("Extracted G1 side, [1]_1 point: {}".format(powers_of_x[0]))

        # Search for start of G2 points. We again know that the first point is the generator.
        pos = SETUP_FILE_G1_STARTPOS + 32 * powers * 2

        # Generator for twisted curve over FQ2
        #    G2 = (
        #        FQ2([
        #            10857046999023057135944570762232829481370756359578518086990519993285655852781,
        #            11559732032986387107991004021392285783925812861821192530917403151452391805634,
        #        ]),
        #        FQ2([
        #            8495653923123431417604973247489272438418190587263600148770280649306958101930,
        #            4082367875863433681332203403145435568316851327593401208105741076214120093531,
        #        ]),
        #    )
        # target?
        target = (factor * b.G2[0].coeffs[0]).n
        while pos < len(contents):
            v = int.from_bytes(contents[pos : pos + 32], "little")
            if v == target:
                break
            pos += 1
        print("Detected start of G2 side at byte {}".format(pos))
        X2_encoding = contents[pos + 32 * 4 : pos + 32 * 8]
        X2_values = [
            b.FQ(int.from_bytes(X2_encoding[i : i + 32], "little")) / factor
            for i in range(0, 128, 32)
        ]
        X2 = (b.FQ2(X2_values[:2]), b.FQ2(X2_values[2:]))
        
        # Curve is y**2 = x**3 + 3
        # b = FQ(3)
        # Twisted curve over FQ**2
        # b2 = FQ2([3, 0]) / FQ2([9, 1])
        assert b.is_on_curve(X2, b.b2)

        print("Extracted G2 side, X^1 point: {}".format(X2))
        # assert b.pairing(b.G2, powers_of_x[1]) == b.pairing(X2, b.G1)
        # print("X^1 points checked consistent")
        return cls(powers_of_x, X2)

    # Encodes the KZG commitment that evaluates to the given values in the group
    def commit(self, values: Polynomial) -> G1Point:
        assert values.basis == Basis.LAGRANGE

        # Run inverse FFT to convert values from Lagrange basis to monomial basis
        # Optional: Check values size does not exceed maximum power that setup can handle
        # Compute linear combination of setup with values
        print("length of polynomial by lagrange basis: ", len(values.values))
        values_mono = values.ifft().values
        print("length of polynomial by monomial basis: ", len(values_mono))
        # assert (len(values_mono) <= len(self.powers_of_x))
        if(len(values_mono) > len(self.powers_of_x)) :
            assert("length of polynomial exceeds maximum power")

        print("length of powers_of_x: ", len(self.powers_of_x))       
        return ec_lincomb([(i, j) for i, j in zip (self.powers_of_x, values_mono)])

    # Generate the verification key for this program with the given setup
    def verification_key(self, pk: CommonPreprocessedInput) -> VerificationKey:
        # Create the appropriate VerificationKey object
        
        group_order = pk.group_order
        QM_commit = self.commit(pk.QM)
        QL_commit = self.commit(pk.QL)
        QR_commit = self.commit(pk.QR)
        QO_commit = self.commit(pk.QO)
        QC_commit = self.commit(pk.QC)
        S1_commit = self.commit(pk.S1)
        S2_commit = self.commit(pk.S2)
        S3_commit = self.commit(pk.S3)

        w = Scalar.root_of_unity(group_order)
        print("group_order: ", group_order)
        print("root of unity w: ", w)
        
        return VerificationKey(group_order, QM_commit, QL_commit, QR_commit, QO_commit, QC_commit, S1_commit, S2_commit, S3_commit, self.X2, w)

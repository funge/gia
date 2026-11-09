"""Independent exact arithmetic checks of native sqrt expected-bit vectors.

This is a test oracle only, not the hardware runtime or a proof of its adapter.
For nonnegative values, squaring checks enclosure without using a sqrt library.
"""
from fractions import Fraction
import unittest


def binary64(bits):
    sign = -1 if bits >> 63 else 1
    exponent = (bits >> 52) & 0x7ff
    fraction = bits & ((1 << 52) - 1)
    if exponent == 0x7ff:
        raise ValueError("finite vectors only")
    significand = fraction if exponent == 0 else (1 << 52) + fraction
    power = -1074 if exponent == 0 else exponent - 1023 - 52
    return sign * Fraction(significand) * Fraction(2) ** power


class HardwareSqrtVectorTests(unittest.TestCase):
    def test_inexact_vectors_bracket_and_are_adjacent(self):
        # Expected bits also tested against actual native execution in Main.lean.
        for operand, lower, upper in [
            (0x4000000000000000, 0x3ff6a09e667f3bcc, 0x3ff6a09e667f3bcd),
            (0x7fefffffffffffff, 0x5fefffffffffffff, 0x5ff0000000000000),
        ]:
            with self.subTest(operand=hex(operand)):
                x, lo, hi = map(binary64, (operand, lower, upper))
                self.assertGreaterEqual(lo, 0)
                self.assertLess(lo * lo, x)
                self.assertLess(x, hi * hi)
                self.assertEqual(upper, lower + 1)

    def test_smallest_subnormal_has_exact_normal_root(self):
        root = binary64(0x1e60000000000000)
        self.assertEqual(root * root, binary64(1))
        self.assertGreater(root, 0)

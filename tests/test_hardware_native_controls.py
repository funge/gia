"""Negative controls for the independent native oracle and instruction gate."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = spec_from_file_location("native_oracle", ROOT / "hardware/check_native.py")
oracle = module_from_spec(spec)
spec.loader.exec_module(oracle)


class NativeOracleControls(unittest.TestCase):
    def test_halfway_downward_and_upward_are_both_required(self):
        case = (0, 0x3FF0000000000000, 0x3CA0000000000000)
        oracle.verify(case, 1, 0x3FF0000000000000, 0x3FF0000000000001)
        for bad in [(0x3FF0000000000000, 0x3FF0000000000000),
                    (0x3FF0000000000001, 0x3FF0000000000001)]:
            with self.assertRaises(AssertionError):
                oracle.verify(case, 1, *bad)

    def test_unknown_does_not_vacuously_pass_finite_cases(self):
        with self.assertRaises(AssertionError):
            oracle.verify((2, 1, 0x3FE0000000000000), 0, 0, 0)

    def test_both_signed_subnormal_underflows_must_enclose(self):
        for sign in (0, oracle.SIGN):
            with self.assertRaises(AssertionError):
                oracle.verify((3, sign | 1, 0x4000000000000000), 1, sign, sign)

    def test_nonfinite_overflow_and_poles_must_be_unknown(self):
        for case in [(0, 0x7FF0000000000001, 0),
                     (0, oracle.MAX, oracle.MAX),
                     (0, oracle.MAX | oracle.SIGN, oracle.MAX | oracle.SIGN),
                     (3, 0x3FF0000000000000, 0),
                     (4, 0xBFF0000000000000, 0)]:
            oracle.verify(case, 0, 0, 0)
            with self.assertRaises(AssertionError):
                oracle.verify(case, 1, 0, 0)

    def test_sqrt_oracle_rejects_inward_bounds(self):
        case = (4, 0x4000000000000000, 0)
        oracle.verify(case, 1, 0x3FF6A09E667F3BCC, 0x3FF6A09E667F3BCD)
        with self.assertRaises(AssertionError):
            oracle.verify(case, 1, 0x3FF6A09E667F3BCD, 0x3FF6A09E667F3BCD)


class InstructionGateControls(unittest.TestCase):
    def check(self, text, arch):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "object.txt"
            path.write_text(text)
            return subprocess.run([sys.executable, str(ROOT / "hardware/check_instructions.py"),
                                   str(path), arch], capture_output=True).returncode

    def test_arm64_requires_scalar_double_and_all_five_operations(self):
        good = "file format mach-o arm64\n" + "\n".join(
            f"{op} d0, d1" + (", d2" if op != "fsqrt" else "")
            for op in ("fadd", "fsub", "fmul", "fdiv", "fsqrt"))
        self.assertEqual(self.check(good, "arm64"), 0)
        for bad in (good.replace("d0", "s0"), good.replace("d0", "v0.2d"),
                    good.replace("fsqrt", "sqrt"), good.replace("arm64", "x86-64")):
            self.assertNotEqual(self.check(bad, "arm64"), 0)

    def test_optimization_cannot_disable_qualification(self):
        for script in ("check_native.py", "check_instructions.py"):
            result = subprocess.run([sys.executable, "-O", str(ROOT / "hardware" / script)],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("assertions enabled", result.stderr)

    def test_x86_requires_scalar_double(self):
        good = "file format elf64-x86-64\naddsd subsd mulsd divsd sqrtsd\n"
        self.assertEqual(self.check(good, "x86_64"), 0)
        self.assertNotEqual(self.check(good.replace("sd", "ss"), "x86_64"), 0)
        self.assertNotEqual(self.check(good, "aarch64"), 0)

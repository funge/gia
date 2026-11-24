"""Compile and run the proof-backed rational search; no floating-point backend."""
import pathlib
import subprocess
import unittest

PROJECT = pathlib.Path(__file__).resolve().parents[1]


class AccuracyExecutionTests(unittest.TestCase):
    def test_compiled_search_rejects_prefix_and_returns_certificate(self):
        result = subprocess.run(
            ["bash", "experiments/accuracy_search/check.sh"], cwd=PROJECT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(
            "compiled search: rejected stages 0,1; selected 2; bounds [2,2]; tolerance 1/100",
            result.stdout,
        )

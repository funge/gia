"""Integration controls: run Lean and assert its process fails on forbidden axioms.

Run from the repository root after `lake build AuditPolicy`:
    python3 -m unittest discover -s tests -v
Fixtures are temporary and are never imported by the project audit.
"""
import pathlib
import subprocess
import tempfile
import unittest

PROJECT = pathlib.Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    def run_lean(self, source):
        with tempfile.TemporaryDirectory(prefix="gia-audit-") as directory:
            path = pathlib.Path(directory) / "Fixture.lean"
            path.write_text("import AuditPolicy\n" + source, encoding="utf-8")
            return subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=PROJECT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=60, check=False,
            )

    def test_axiom_free_passes(self):
        result = self.run_lean("theorem harmless : True := True.intro\n#audit_axioms harmless\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("axiom audit passed harmless: []", result.stdout)

    def test_allowlisted_axioms_pass(self):
        result = self.run_lean(
            "#audit_axioms propext\n#audit_axioms Classical.choice\n#audit_axioms Quot.sound\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(result.stdout.count("axiom audit passed"), 3)

    def test_sorry_dependency_fails(self):
        result = self.run_lean("theorem unfinished : False := by sorry\n#audit_axioms unfinished\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("axiom audit rejected unfinished", result.stdout)
        self.assertIn("sorryAx", result.stdout)

    def test_transitive_custom_axiom_fails(self):
        result = self.run_lean(
            "axiom forbidden : False\ndef intermediate : False := forbidden\n"
            "theorem indirect : False := intermediate\n#audit_axioms indirect\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("axiom audit rejected indirect", result.stdout)
        self.assertIn("forbidden", result.stdout)

    def test_namespace_catches_unlisted_axiom(self):
        result = self.run_lean(
            "namespace AuditFixture\naxiom unlisted : False\n"
            "theorem harmless : True := True.intro\nend AuditFixture\n"
            "#audit_axioms AuditFixture.harmless\n#audit_namespace AuditFixture\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("axiom audit rejected AuditFixture.unlisted", result.stdout)

    def test_namespace_catches_unlisted_sorry(self):
        result = self.run_lean(
            "namespace AuditFixture\ntheorem unlisted : False := by sorry\n"
            "end AuditFixture\n#audit_namespace AuditFixture\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("axiom audit rejected AuditFixture.unlisted", result.stdout)
        self.assertIn("sorryAx", result.stdout)

    def test_unknown_name_fails(self):
        result = self.run_lean("#audit_axioms ThisNameDoesNotExist\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_empty_namespace_fails(self):
        result = self.run_lean("#audit_namespace NoSuchNamespace\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("has no theorem or axiom declarations", result.stdout)


if __name__ == "__main__":
    unittest.main()

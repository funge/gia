"""Standalone pinned API inventory; optional explicit checkout drift check."""
import hashlib
import json
import os
import pathlib
import re
import unittest

PROJECT = pathlib.Path(__file__).resolve().parents[1]
INVENTORY = PROJECT / 'provenance/relgraph-api.json'


def public_functions(text):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.findall(r"\b(gi_\w+)\s*\([^;{}]*\)\s*;", text)


def compare_checkout(root, inventory):
    """Return errors; never auto-discover, clone or modify a C checkout."""
    errors = []
    directory = root / 'include/graphing'
    expected = {h['path'] for h in inventory['headers']}
    actual = {p.relative_to(root).as_posix() for p in directory.glob('*.h')}
    if actual != expected:
        errors.append('header inventory differs')
    for h in inventory['headers']:
        path = root / h['path']
        if not path.is_file():
            errors.append(f"missing {h['path']}")
            continue
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != h['sha256']:
            errors.append(f"content differs: {h['path']}")
        if public_functions(data.decode()) != h['symbols']:
            errors.append(f"symbols differ: {h['path']}")
    return errors


class OperationCoverageTests(unittest.TestCase):
    def test_pinned_inventory_ledger_is_exact(self):
        inventory = json.loads(INVENTORY.read_text())
        self.assertEqual(inventory['commit'], '7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b')
        symbols = [s for h in inventory['headers'] for s in h['symbols']]
        self.assertTrue(symbols)
        self.assertEqual(len(symbols), len(set(symbols)))
        for h in inventory['headers']:
            self.assertRegex(h['git_blob'], r'^[a-f0-9]{40}$')
            self.assertRegex(h['sha256'], r'^[a-f0-9]{64}$')
        ledger = (PROJECT / 'OPERATION_COVERAGE.md').read_text()
        rows = re.findall(r'^\| \[`(gi_\w+)`\]\([^)]*\) \|', ledger, flags=re.M)
        self.assertEqual(len(rows), len(set(rows)), 'duplicate coverage rows')
        self.assertCountEqual(symbols, rows)

    @unittest.skipUnless(os.environ.get('RELGRAPH_CHECKOUT'), 'optional explicit C checkout comparison')
    def test_explicit_checkout_matches_inventory(self):
        errors = compare_checkout(pathlib.Path(os.environ['RELGRAPH_CHECKOUT']).resolve(),
                                  json.loads(INVENTORY.read_text()))
        self.assertEqual(errors, [])

    def test_missing_checkout_is_not_silently_accepted(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            self.assertTrue(compare_checkout(pathlib.Path(directory), json.loads(INVENTORY.read_text())))

    def test_changed_header_is_detected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / 'include/graphing/example.h'
            path.parent.mkdir(parents=True)
            original = b'double gi_example(void);'
            entry = {'path': 'include/graphing/example.h', 'sha256': hashlib.sha256(original).hexdigest(),
                     'symbols': ['gi_example']}
            path.write_bytes(original)
            self.assertEqual(compare_checkout(root, {'headers': [entry]}), [])
            path.write_bytes(b'double gi_different(void);')
            self.assertEqual(len(compare_checkout(root, {'headers': [entry]})), 2)

    def test_multiline_and_comment_declarations(self):
        self.assertEqual(public_functions('/* gi_fake(void); */\ndouble gi_real(\n int x);'), ['gi_real'])

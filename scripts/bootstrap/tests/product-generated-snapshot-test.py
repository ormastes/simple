"""SCV evidence-parser regression fixtures; these do not qualify a compiler."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class GeneratedSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='generated snapshot ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.generated = self.root / 'src/app'
        self.snapshot = self.root / 'build/scv/snapshots/frozen'
        self.generated.mkdir(parents=True)
        self.snapshot.mkdir(parents=True)
        self.receipts = self.root / 'build/scv/receipts'
        self.receipts.mkdir(parents=True)
        self.files = {'product/main.spl': b'fn main() -> i64:\n    0\n',
                      'product/owner.spl': b'fn check() -> bool:\n    true\n'}
        manifest = 'path\tsha256\n'
        inventory = ''
        for name, data in self.files.items():
            sha = hashlib.sha256(data).hexdigest()
            for root in (self.generated, self.snapshot / 'src/app'):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            manifest += name + '\t' + sha + '\n'
            inventory += 'src/app/' + name + '|sha256_' + sha + '|' + str(len(data)) + '\n'
        self.manifest = self.generated / 'generated-manifest.tsv'
        self.manifest.write_text(manifest, newline='\n')
        (self.snapshot / 'SCV_COMPILE_INVENTORY').write_text(inventory, newline='\n')
        self.revision = 'scv-revision-v1-' + 'a' * 64
        raw = ('simple-scv-compile-snapshot-v1\nrevision=' + self.revision +
               '\ninventory=' + hashlib.sha256(inventory.encode()).hexdigest() + '\ncount=2\n')
        (self.snapshot / 'SCV_COMPILE_SNAPSHOT').write_text(raw, newline='\n')
        self.receipt = self.receipts / (self.revision + '.receipt')
        self.receipt.write_text(raw + 'completed=true\n', newline='\n')
        self.output = self.root / 'proof.env'

    def run_checker(self):
        perl = os.environ.get('BOOTSTRAP_TEST_PERL') or shutil.which('perl')
        if not perl:
            self.skipTest('Perl unavailable')
        return subprocess.run([perl, str(Path(__file__).parents[1] /
            'verify-product-generated-snapshot.pl'), str(self.root), str(self.generated),
            str(self.manifest), str(self.output)], capture_output=True, text=True)

    def test_complete_generated_membership(self):
        result = self.run_checker()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('generated_files=2\n', self.output.read_text())
        self.assertIn('status=generated-membership-verified\n', self.output.read_text())

    def test_current_pointer_cannot_replace_completed_receipt(self):
        self.receipt.unlink()
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.output.exists())

    def test_snapshot_payload_mutation_rejected(self):
        (self.snapshot / 'src/app/product/owner.spl').write_bytes(b'changed')
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('payload differs', result.stderr)

    def test_rendered_source_mutation_rejected(self):
        (self.generated / 'product/main.spl').write_bytes(b'changed')
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('rendered source changed', result.stderr)


if __name__ == '__main__':
    unittest.main()

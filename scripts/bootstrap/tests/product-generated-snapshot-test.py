"""SCV evidence-parser regression fixtures; these do not qualify a compiler."""
import hashlib
import os
from pathlib import Path
import shutil
import shlex
import subprocess
import tempfile
import unittest


class GeneratedSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='generated snapshot ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.generated = self.root / 'src/app'
        self.snapshot = self.root / 'build/scv/snapshots/staging-fixture'
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
        self.publish_inventory(inventory.rstrip('\n'))
        self.output = self.root / 'proof.env'

    def publish_inventory(self, inventory):
        digest = hashlib.sha256(inventory.encode()).hexdigest()
        tree = 'scv-tree-v1-' + digest
        count = len(inventory.splitlines())
        self.revision = 'scv-revision-v1-' + hashlib.sha256(
            f'simple/scv-compile-revision/v1|{tree}|{digest}'.encode()).hexdigest()
        commit = 'scv-compile-v1-' + hashlib.sha256(
            f'simple/scv-compile-commit/v1|{tree}|{count}'.encode()).hexdigest()
        final = self.snapshot.parent / self.revision
        self.snapshot.rename(final)
        self.snapshot = final
        (self.snapshot / 'SCV_COMPILE_INVENTORY').write_text(inventory, newline='\n')
        raw = (f'simple-scv-compile-snapshot-v1\nrevision={self.revision}\ncommit={commit}'
               f'\ntree={tree}\ninventory={digest}\ncount={count}')
        (self.snapshot / 'SCV_COMPILE_SNAPSHOT').write_text(raw, newline='\n')
        self.receipt = self.receipts / (self.revision + '.receipt')
        self.receipt.write_text(raw + '\nsnapshot=snapshots/' + self.revision, newline='\n')

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

    def test_generated_test_owner_missing_from_valid_snapshot_is_rejected(self):
        inventory = (self.snapshot / 'SCV_COMPILE_INVENTORY').read_text()
        self.publish_inventory(inventory.splitlines()[0])
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('exactly one completed generated-product snapshot', result.stderr)
        self.assertFalse(self.output.exists())

    def test_provenance_prefix_is_not_a_completed_receipt(self):
        self.receipt.write_bytes((self.snapshot / 'SCV_COMPILE_SNAPSHOT').read_bytes())
        result = self.run_checker()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('no completed receipt', result.stderr)
        self.assertFalse(self.output.exists())

    def test_readonly_replay_matches_saved_proof(self):
        first = self.run_checker()
        self.assertEqual(first.returncode, 0, first.stderr)
        perl = os.environ.get('BOOTSTRAP_TEST_PERL') or shutil.which('perl')
        result = subprocess.run([perl, str(Path(__file__).parents[1] /
            'verify-product-generated-snapshot.pl'), str(self.root), str(self.generated),
            str(self.manifest), '-'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, self.output.read_text())

    def run_builder_publication_fragment(self):
        # Execute the actual builder's post-compile authority gate. The compile
        # command is deliberately mocked: this is a caller-wiring test only.
        bootstrap = Path(__file__).parents[1]
        source = (bootstrap / 'build-compiler-subsystem-test-product.shs').read_text()
        fragment = source[source.index('run_native_build product src/app/product/main.spl'):
                          source.index('backend_identity="$job_root/cache-product/')]
        job = self.root / 'job'
        (job / 'logs').mkdir(parents=True)
        values = {'tool_root': bootstrap.parents[1], 'overlay': self.root,
                  'generated': self.generated, 'manifest': self.manifest,
                  'job_root': job, 'output': job / 'not-a-real-binary', 'backend': 'cranelift'}
        script = 'set -eu\nrun_native_build() { return 0; }\nfail() { echo "$1" >&2; exit 37; }\n'
        script += '\n'.join(key + '=' + shlex.quote(str(value).replace('\\', '/'))
                            for key, value in values.items()) + '\n'
        script += fragment + '\nprintf caller_gate_passed\\n\n'
        bash = os.environ.get('BOOTSTRAP_TEST_BASH') or shutil.which('bash')
        if not bash:
            self.skipTest('Bash unavailable')
        return subprocess.run([bash, '--noprofile', '--norc', '-c', script],
                              capture_output=True, text=True), job

    def test_builder_gate_publishes_proof_for_actual_generated_membership(self):
        result, job = self.run_builder_publication_fragment()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('generated_files=2', (job / 'logs/generated-source-snapshot.env').read_text())

    def test_builder_gate_stops_when_generated_test_owner_is_missing(self):
        inventory = (self.snapshot / 'SCV_COMPILE_INVENTORY').read_text()
        self.publish_inventory(inventory.splitlines()[0])
        result, job = self.run_builder_publication_fragment()
        self.assertEqual(result.returncode, 37, result.stderr)
        self.assertIn('generated test sources absent', result.stderr)
        self.assertFalse((job / 'logs/generated-source-snapshot.env').exists())


if __name__ == '__main__':
    unittest.main()

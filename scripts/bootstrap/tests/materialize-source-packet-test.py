"""Exercise the real successor caller on a tiny authenticated Git archive."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

SCRIPTS = Path(__file__).parents[1]
REQUIRED = [
    'src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h',
    'tools/counterpart/sdk/c/simple_counterpart_abi.h', 'src/app/t32_cli/mod.spl',
    'src/runtime/runtime_native.c', 'src/runtime/runtime.h',
    'src/app/cli/interpreter_main.spl',
    'src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl',
    'scripts/bootstrap/bootstrap-logged-process.shs', 'config/var.sdn',
    'scripts/resource/fixture.txt']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.PIPE)


class CallerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temp.cleanup)
        cls.base = Path(cls.temp.name)
        cls.repo = cls.base / 'repo'
        cls.repo.mkdir()
        git(cls.repo, 'init', '--quiet')
        for name in REQUIRED:
            path = cls.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(('fixture ' + name + '\n').encode())
        git(cls.repo, 'add', '--', '.')
        git(cls.repo, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
            '-c', 'core.hooksPath=NUL', 'commit', '--quiet', '-m', 'fixture')
        cls.head = git(cls.repo, 'rev-parse', 'HEAD').decode().strip()
        cls.archive = cls.base / 'source.tar'
        with cls.archive.open('wb') as output:
            subprocess.run(['git', '-C', str(cls.repo), 'archive', cls.head],
                           stdout=output, check=True)

    def setUp(self):
        self.packet = self.base / self._testMethodName
        self.packet.mkdir()
        self.root = self.packet / 'source'
        git(self.repo, 'worktree', 'add', '--detach', '--no-checkout', str(self.root), self.head)
        git(self.root, 'read-tree', 'HEAD')
        for name in ('materialize-source-packet.py', 'materialization-path-boundary.py'):
            shutil.copyfile(SCRIPTS / name, self.packet / name)
        self.helper = self.packet / 'materialization-path-boundary.py'
        self.config = dict(schema='bootstrap-materialization-request-v1',
            source_root=str(self.root), repository=str(self.repo), source_head=self.head,
            archive_source_head=self.head, archive_path=str(self.archive),
            archive_sha256=digest(self.archive), boundary_helper_sha256=digest(self.helper))

    def run_caller(self):
        request = self.packet / 'request.json'
        request.write_text(json.dumps(self.config), encoding='utf8')
        return subprocess.run([sys.executable, str(self.packet / 'materialize-source-packet.py'),
            '--config', str(request), '--config-sha256', digest(request)],
            capture_output=True, text=True)

    def test_real_archive_authentication_and_pinned_ready_receipt(self):
        result = self.run_caller()
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        ready = json.loads((self.packet / 'source-ready.json').read_text())
        self.assertEqual(ready['authenticated_regular_blobs'], len(REQUIRED))
        self.assertEqual(ready['boundary_helper_sha256'], digest(self.helper))
        self.assertEqual(ready['materializer_sha256'], digest(self.packet / 'materialize-source-packet.py'))
        self.assertEqual(ready['materialization_request_sha256'], digest(self.packet / 'request.json'))
        self.assertFalse(ready['native_verified'])
        for name in REQUIRED:
            self.assertEqual((self.root / name).read_bytes(), git(self.repo, 'show', self.head + ':' + name))

    def test_tampered_helper_rejected_before_execution(self):
        marker = self.packet / 'executed'
        self.helper.write_text(f'from pathlib import Path\nPath({str(marker)!r}).touch()\n')
        result = self.run_caller()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('boundary helper hash mismatch', result.stderr)
        self.assertFalse(marker.exists())
        self.assertFalse((self.packet / 'source-ready.json').exists())

    def test_archive_hash_mismatch_cannot_publish(self):
        self.config['archive_sha256'] = '0' * 64
        result = self.run_caller()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('archive hash mismatch', result.stderr)
        self.assertFalse((self.packet / 'source-ready.json').exists())

    def test_reused_archive_restores_new_blob_and_preserves_repaired_original(self):
        changed = 'config/var.sdn'
        added = 'test/new-fixture.spl'
        with tarfile.open(self.archive) as archive:
            before = archive.extractfile(changed).read()
        (self.repo / changed).write_bytes(b'updated candidate configuration\n')
        (self.repo / added).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / added).write_bytes(b'new candidate fixture\n')
        git(self.repo, 'add', '--', changed, added)
        git(self.repo, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
            '-c', 'core.hooksPath=NUL', 'commit', '--quiet', '-m', 'candidate delta')
        revision = git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        git(self.root, 'update-ref', 'HEAD', revision)
        git(self.root, 'read-tree', 'HEAD')
        self.config['source_head'] = revision
        result = self.run_caller()
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        ready = json.loads((self.packet / 'source-ready.json').read_text())
        self.assertEqual(ready['authenticated_regular_blobs'], len(REQUIRED) + 1)
        self.assertEqual([row['path'] for row in ready['archive_omissions_restored']], [added])
        # Windows archive export can also apply CRLF to unchanged Git blobs.
        repairs = {row['path']: row for row in ready['archive_transform_repairs']}
        self.assertIn(changed, repairs)
        self.assertFalse(repairs[changed]['crlf_only'])
        self.assertTrue(all(row['crlf_only'] for name, row in repairs.items() if name != changed))
        self.assertEqual((self.packet / 'archive-transformed-originals' / changed).read_bytes(), before)
        self.assertEqual((self.root / changed).read_bytes(), (self.repo / changed).read_bytes())
        self.assertEqual((self.root / added).read_bytes(), (self.repo / added).read_bytes())

    def test_root_replacement_at_publication_cannot_publish(self):
        # Fault injection into a separately pinned test helper: perform the root
        # replacement only at the real caller's final verification boundary.
        with self.helper.open('a') as output:
            output.write('''
OriginalBoundary = MaterializationBoundary
class MaterializationBoundary(OriginalBoundary):
    def verify_root(self):
        self.root.rename(self.root.with_name('original-source'))
        self.root.mkdir()
        return super().verify_root()
''')
        self.config['boundary_helper_sha256'] = digest(self.helper)
        result = self.run_caller()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('materialization root changed before publication', result.stderr)
        self.assertTrue((self.packet / 'physical-git-blobs-final.tsv').exists())
        self.assertFalse((self.packet / 'source-ready.json').exists())


if __name__ == '__main__':
    unittest.main()

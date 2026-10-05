#!/usr/bin/env python3
"""Focused rejection checks for source/tool authority separation."""
import importlib.util
import json
import os
import shutil
import sys
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('authority',
    Path(__file__).parents[1] / 'tool-code-authority.py')
authority = importlib.util.module_from_spec(spec)
spec.loader.exec_module(authority)


class ToolAuthorityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'tools'
        self.root.mkdir()
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        self.entry = self.root / 'scripts/bootstrap/entry.shs'
        self.entry.parent.mkdir(parents=True)
        self.entry.write_text('echo pinned\n', newline='\n')
        self.facade = self.root / 'scripts/check/lib/facade.shs'
        self.facade.parent.mkdir(parents=True)
        self.facade.write_text('true\n', newline='\n')
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Test',
            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture'], check=True)
        head = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        self.manifest = Path(self.temp.name) / 'tools.json'
        self.value = dict(schema='simple-bootstrap-tool-code-v1', tool_head=head,
            files={p.relative_to(self.root).as_posix(): authority.sha(p)
                   for p in (self.entry, self.facade)})
        self.pin()

    def pin(self):
        self.manifest.write_text(json.dumps(self.value), newline='\n')
        self.expected = authority.sha(self.manifest)

    def validate(self):
        return authority.validate(self.root, self.manifest, self.expected, self.entry)

    def test_separate_source_is_not_tool_authority(self):
        source = Path(self.temp.name) / 'source'
        source.mkdir()
        (source / 'compiler.spl').write_text('frozen source', newline='\n')
        self.assertEqual(self.validate()['tool_head'], self.value['tool_head'])
        self.assertEqual((source / 'compiler.spl').read_text(), 'frozen source')

    def test_modified_transitive_tool_rejected(self):
        self.facade.write_text('false\n', newline='\n')
        with self.assertRaisesRegex(ValueError, 'tool bytes differ'):
            self.validate()

    def test_unlisted_import_rejected(self):
        (self.entry.parent / 'injected.py').write_text('raise RuntimeError()', newline='\n')
        with self.assertRaisesRegex(ValueError, 'complete physical closure'):
            self.validate()

    def test_manifest_tamper_rejected(self):
        self.manifest.write_text('{}', newline='\n')
        with self.assertRaisesRegex(ValueError, 'manifest identity'):
            self.validate()

    def test_stale_commit_rejected(self):
        self.value['tool_head'] = '0' * 40
        self.pin()
        with self.assertRaisesRegex(ValueError, 'tool commit differs'):
            self.validate()

    def test_unbound_entry_rejected(self):
        with self.assertRaises(ValueError):
            authority.validate(self.root, self.manifest, self.expected,
                               Path(self.temp.name) / 'outside.py')

    def test_shell_uses_tool_root_and_keeps_source_root(self):
        shell = os.environ.get('BOOTSTRAP_TEST_SHELL') or shutil.which('bash')
        if not shell:
            self.skipTest('POSIX shell unavailable')
        source = Path(self.temp.name) / 'source'
        source.mkdir()
        validator = self.entry.parent / 'tool-code-authority.py'
        validator.write_bytes((Path(__file__).parents[1] / validator.name).read_bytes())
        library = self.entry.parent / 'lib/product-tool-authority.shs'
        library.parent.mkdir()
        library.write_bytes((Path(__file__).parents[1] / 'lib' / library.name).read_bytes())
        self.entry.write_text('set -eu\nsource_root="$1"\n'
            'script_root=$(CDPATH= cd -P -- "$(dirname -- "$0")" && pwd -P)\n'
            '. "$script_root/lib/product-tool-authority.shs"\n'
            '[ "$tool_root" != "$source_root" ]\n'
            'printf "%s\\n" "$source_root" "$tool_root"\n'
            'bootstrap_product_tool_verify\n', newline='\n')
        self.value['files'] = {p.relative_to(self.root).as_posix(): authority.sha(p)
            for p in (self.entry, self.facade, validator, library)}
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Test',
            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'shell fixture'], check=True)
        self.value['tool_head'] = subprocess.check_output(
            ['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        self.pin()
        env = dict(os.environ, SIMPLE_BOOTSTRAP_TOOL_ROOT=self.root.as_posix(),
            SIMPLE_BOOTSTRAP_TOOL_MANIFEST=self.manifest.as_posix(),
            SIMPLE_BOOTSTRAP_TOOL_MANIFEST_SHA256=self.expected,
            SIMPLE_BOOTSTRAP_TOOL_PYTHON=Path(sys.executable).as_posix())
        run = subprocess.run([shell, self.entry.as_posix(), source.as_posix()],
                             env=env, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(len(run.stdout.splitlines()), 2)
        self.assertTrue(run.stdout.splitlines()[0].endswith('/source'))
        self.assertTrue(run.stdout.splitlines()[1].endswith('/tools'))
        self.facade.write_text('changed after pin\n', newline='\n')
        rejected = subprocess.run([shell, self.entry.as_posix(), source.as_posix()],
                                  env=env, capture_output=True, text=True)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn('tool bytes differ', rejected.stderr)

    def test_rehashed_dirty_tool_cannot_claim_committed_identity(self):
        self.entry.write_text('echo unreviewed\n', newline='\n')
        self.value['files'][self.entry.relative_to(self.root).as_posix()] = authority.sha(self.entry)
        self.pin()
        with self.assertRaisesRegex(ValueError, 'not from pinned commit'):
            self.validate()


if __name__ == '__main__':
    unittest.main()

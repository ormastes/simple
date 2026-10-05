#!/usr/bin/env python3
"""Focused rejection checks for source/tool authority separation."""
import importlib.util
import json
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
        self.entry.write_text('echo pinned\n')
        self.facade = self.root / 'scripts/check/lib/facade.shs'
        self.facade.parent.mkdir(parents=True)
        self.facade.write_text('true\n')
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
        self.manifest.write_text(json.dumps(self.value))
        self.expected = authority.sha(self.manifest)

    def validate(self):
        return authority.validate(self.root, self.manifest, self.expected, self.entry)

    def test_separate_source_is_not_tool_authority(self):
        source = Path(self.temp.name) / 'source'
        source.mkdir()
        (source / 'compiler.spl').write_text('frozen source')
        self.assertEqual(self.validate()['tool_head'], self.value['tool_head'])
        self.assertEqual((source / 'compiler.spl').read_text(), 'frozen source')

    def test_modified_transitive_tool_rejected(self):
        self.facade.write_text('false\n')
        with self.assertRaisesRegex(ValueError, 'tool bytes differ'):
            self.validate()

    def test_unlisted_import_rejected(self):
        (self.entry.parent / 'injected.py').write_text('raise RuntimeError()')
        with self.assertRaisesRegex(ValueError, 'complete physical closure'):
            self.validate()

    def test_manifest_tamper_rejected(self):
        self.manifest.write_text('{}')
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


if __name__ == '__main__':
    unittest.main()

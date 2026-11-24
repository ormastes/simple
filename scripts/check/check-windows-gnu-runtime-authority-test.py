#!/usr/bin/env python3
"""Format admission checks; fixture headers are not compiled runtime evidence."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('authority',
    Path(__file__).with_name('check-windows-gnu-runtime-authority.py'))
authority = importlib.util.module_from_spec(spec)
spec.loader.exec_module(authority)


class ArchiveFormats(unittest.TestCase):
    def test_native_and_import_members(self):
        self.assertEqual(authority.validate_formats(
            'Format: COFF-x86-64\nFormat: COFF-import-file-x86-64\n'),
            {'COFF-import-file-x86-64': 1, 'COFF-x86-64': 1})

    def test_rejects_wrong_or_missing_members(self):
        for headers in ('', 'Format: ELF64-x86-64\n',
                        'Format: COFF-x86-64\nFormat: ELF64-x86-64\n',
                        'Format: COFF-ARM64\n', 'Format: COFF-import-file-x86-64\n'):
            with self.subTest(headers=headers), self.assertRaises(ValueError):
                authority.validate_formats(headers)


if __name__ == '__main__':
    unittest.main()

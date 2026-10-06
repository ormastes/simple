import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('wave',
    Path(__file__).parents[1] / 'run-bootstrap-test-wave.py')
wave = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wave)


class ValidatorImportTests(unittest.TestCase):
    def test_tampered_validator_is_rejected_before_side_effect(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            validator = root / 'scripts/bootstrap/tool-code-authority.py'
            validator.parent.mkdir(parents=True)
            validator.write_text('pinned = True\n')
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps(dict(schema='simple-bootstrap-tool-code-v1',
                files={'scripts/bootstrap/tool-code-authority.py': wave.digest(validator)})))
            expected = wave.digest(manifest)
            sentinel = root / 'executed'
            validator.write_text('from pathlib import Path\nPath(' + repr(str(sentinel)) +
                                 ').write_text("must never execute")\n')
            with self.assertRaisesRegex(ValueError, 'before import'):
                wave.load_tool_authority(root, manifest, expected)
            self.assertFalse(sentinel.exists())


if __name__ == '__main__':
    unittest.main()

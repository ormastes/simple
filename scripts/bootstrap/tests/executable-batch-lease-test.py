"""Exercise the actual lease cleanup helper; never launch a compiler."""
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

HELPER = pathlib.Path(__file__).resolve().parents[1] / 'lib/executable-batch-lease.shs'
BASH = os.environ.get('SIMPLE_BOOTSTRAP_BASH') or shutil.which('bash')

def shell_path(path):
    text = pathlib.Path(path).as_posix()
    if os.name == 'nt':
        return '/' + text[0].lower() + text[2:]
    return text

@unittest.skipUnless(BASH, 'bash required for shell lease contract')
class LeaseTests(unittest.TestCase):
    def test_actual_shell_cleanup_requires_ownership_and_quiescence(self):
        with tempfile.TemporaryDirectory() as name:
            root = pathlib.Path(name)
            lease = root / 'writer.lease'
            receipt = root / 'rss.env'
            for owned, quiet, errors, retained in [
                ('1', '0', '0', True),
                ('1', '1', '1', True),
                ('0', '1', '0', True),
                ('1', '1', '0', False),
            ]:
                lease.write_text('owner\n')
                receipt.write_text('quiescent=' + quiet + '\nobserver_errors=' + errors + '\n')
                command = '. "$1"; executable_batch_release_owned_lease "$2" "$3" 1 "$4"'
                subprocess.run([BASH, '-c', command, 'lease-test', shell_path(HELPER),
                                shell_path(lease), shell_path(receipt), owned], check=True)
                self.assertEqual(lease.exists(), retained)

if __name__ == '__main__':
    unittest.main()

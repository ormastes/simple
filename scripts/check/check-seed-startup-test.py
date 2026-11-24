#!/usr/bin/env python3
"""Exercise the publication gate with real native processes, not compiler claims."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('startup', Path(__file__).with_name('check-seed-startup.py'))
startup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(startup)


class NativeStartupGate(unittest.TestCase):
    def test_native_process_outcomes(self):
        cc = os.environ.get('CC') or shutil.which('clang')
        self.assertTrue(cc, 'CC or clang is required for the real native process fixture')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'fixture.c'
            source.write_text('''#include <stdio.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif
int main(int argc, char **argv) {
  if (argc != 2 || strcmp(argv[1], "--version")) return 9;
  if (strstr(argv[0], "hang")) {
#ifdef _WIN32
    Sleep(60000);
#else
    sleep(60);
#endif
  }
  if (strstr(argv[0], "fail")) return 3;
  puts(strstr(argv[0], "invalid") ? "unrelated program" : "simple native fixture");
  return 0;
}
''', encoding='utf-8')
            binary = root / ('fixture.exe' if os.name == 'nt' else 'fixture')
            subprocess.run([cc, str(source), '-o', str(binary)], check=True, timeout=30)
            for name, status, expected_code in [('good', 'PASS', 0), ('fail', 'FAIL', 3),
                                                  ('invalid', 'FAIL', 0), ('hang', 'TIMEOUT', None)]:
                with self.subTest(name=name):
                    seed = root / (name + binary.suffix)
                    shutil.copy2(binary, seed)
                    output = root / (name + '.json')
                    result = startup.check(seed, output, timeout=0.3 if name == 'hang' else 5)
                    receipt = json.loads(output.read_text(encoding='utf-8'))
                    self.assertEqual(result, 0 if status == 'PASS' else 1)
                    self.assertEqual(receipt['status'], status)
                    self.assertEqual(receipt['exit_code'], expected_code)
                    self.assertEqual(receipt['seed_sha256'], startup.sha256(seed))
                    self.assertEqual(receipt['seed_sha256_after'], receipt['seed_sha256'])
                    self.assertEqual(receipt['command'], [str(seed.resolve()), '--version'])


if __name__ == '__main__':
    unittest.main()

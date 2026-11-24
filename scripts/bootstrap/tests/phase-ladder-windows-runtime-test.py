#!/usr/bin/env python3
"""Execute the production seed argv fragment; fixture is not compiler evidence."""
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[3]
source = (root/'scripts/bootstrap/phase-ladder-step.shs').read_text()
start = source.index('  seed_file_timeout=${PHASE_LADDER_SEED_FILE_TIMEOUT:-1200}')
end = source.index('\nfi\nnext=0', start)
fragment = source[start:end]
with tempfile.TemporaryDirectory(prefix='ladder-runtime-') as directory:
    fixture = Path(directory)
    seed = fixture/'src/compiler_rust/target/bootstrap'
    seed.mkdir(parents=True)
    for name in ('simple', 'simple.exe'):
        path = seed/name
        path.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > captured-argv\n')
        path.chmod(0o755)
    for platform, abi, expected in [('windows-x86_64', '', True),
                                    ('windows-x86_64', 'gnu', True),
                                    ('windows-x86_64', 'msvc', False),
                                    ('linux-x86_64', 'gnu', False),
                                    ('darwin-arm64', '', False)]:
        env = dict(os.environ, platform=platform, SIMPLE_WINDOWS_ABI=abi,
                   exe='.exe' if platform.startswith('windows-') else '',
                   threads='2', cache_root='cache', evidence_root='.')
        subprocess.run(['sh', '-eu', '-c', fragment], cwd=fixture, env=env,
                       check=True, timeout=20)
        argv = (fixture/'captured-argv').read_text().splitlines()
        assert argv[:3] == ['native-build', '--source', 'src/compositions/kernel_llvm_cranelift']
        assert ('--runtime-bundle' in argv) == expected, (platform, abi, argv)
        if expected:
            assert argv[argv.index('--runtime-bundle')+1] == 'core-c-bootstrap'
        display = (fixture/'seed-argv-display.txt').read_text()
        assert ('--runtime-bundle core-c-bootstrap' in display) == expected
print('PASS: actual seed argv selects canonical GNU Windows bundle; other lanes unchanged (fixture only)')

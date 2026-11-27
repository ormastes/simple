#!/usr/bin/env python3
"""Execute the real unchanged-seed guard for both artifact extraction layouts."""
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[3]
source = (root/'scripts/bootstrap/phase-ladder-step.shs').read_text()
start = source.index('  prior_diagnostics=${PHASE_LADDER_PRIOR_DIAGNOSTICS_ROOT:')
end = source.index('  echo "phase-ladder: no qualified compiler;', start)
fragment = source[start:end] + '\nprintf "CONTINUE\\n"\n'
cases = [('single', 'source-a', 'windows-x86_64', 4, 86),
         ('multiple', 'source-a', 'windows-x86_64', 4, 86),
         ('source-changed', 'source-b', 'windows-x86_64', 4, 0),
         ('platform-changed', 'source-a', 'linux-x86_64', 4, 0),
         ('threads-changed', 'source-a', 'windows-x86_64', 2, 0),
         ('absent', 'source-a', 'windows-x86_64', 4, 0)]
with tempfile.TemporaryDirectory(prefix='ladder-receipts-') as directory:
    base = Path(directory)
    for name, revision, platform, threads, expected in cases:
        diagnostics = base/name
        destination = diagnostics/'artifact-r1' if name == 'multiple' else diagnostics
        destination.mkdir(parents=True)
        if name != 'absent':
            (destination/'seed-native-failure.sdn').write_text(
                f'schema: phase-ladder-attempt-v1\nsource_revision: {revision}\n'
                f'platform: {platform}\nseed_threads: {threads}\nadmission: none\n')
        env = dict(os.environ, SIMPLE_WINDOWS_ABI='gnu',
                   PHASE_LADDER_PRIOR_DIAGNOSTICS_ROOT=str(diagnostics),
                   source_revision='source-a', platform='windows-x86_64', threads='4')
        result = subprocess.run(['sh', '-eu', '-c', fragment], env=env,
                                capture_output=True, text=True, timeout=10)
        assert result.returncode == expected, (name, expected, result.returncode, result.stderr)
        if expected:
            assert 'unchanged failed seed blocked' in result.stderr and not result.stdout
        else:
            assert result.stdout.strip() == 'CONTINUE'
print('PASS: production guard rejects matching flat/nested receipts; changed identities and absent receipts continue')

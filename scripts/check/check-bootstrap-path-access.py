"""Test the actual bootstrap PATH block without elevated ACL setup or a build.

Run --script bootstrap-from-scratch.sh --output NEW_PRIVATE_DIRECTORY.
A scoped shell cd shim reproduces directory-exists/traversal-denied behavior;
all other directory traversal uses builtin cd. No caller environment is changed.
"""
import argparse
import json
import pathlib
import subprocess


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--script', required=True, type=pathlib.Path)
    ap.add_argument('--output', required=True, type=pathlib.Path)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    source = args.script.read_text(encoding='utf-8')
    start = source.index('bootstrap_canonical_path=\n')
    end = source.index('export PATH\n', start)+len('export PATH\n')
    block = source[start:end]
    for name in ('readable', 'space directory', 'denied', '.codex/tmp/arg0/session'):
        (args.output/name).mkdir(parents=True)

    def path(name):
        value = str((args.output/name).resolve()).replace('\\', '/')
        return '/'+value[0].lower()+value[2:] if len(value)>1 and value[1]==':' else value

    def quote(value):
        return "'"+value.replace("'", "'\\''")+"'"

    readable, spaced, denied, missing = map(path, ('readable', 'space directory', 'denied', 'missing'))
    # Preserve exact expected path spelling from pwd -P, not Python normalization.
    shell = 'C:/Program Files/Git/bin/bash.exe'
    canonical = {}
    for value in (readable, spaced):
        r = subprocess.run([shell, '-c', 'CDPATH= builtin cd -- "$1" && pwd -P', 'test', value], capture_output=True, check=True)
        canonical[value] = r.stdout.decode().strip()
    cases = [
        ('readable', readable, 0, canonical[readable], False),
        ('missing-and-readable', missing+':'+readable, 0, canonical[readable], False),
        ('untraversable-and-readable', denied+':'+readable, 0, canonical[readable], True),
        ('readable-and-untraversable', readable+':'+denied, 0, canonical[readable], True),
        ('duplicate-canonical-directory', readable+':'+readable+'/../readable', 0, canonical[readable], False),
        ('space-directory', spaced, 0, canonical[spaced], False),
        ('empty', '', 1, None, False),
        ('only-missing', missing, 1, None, False),
        ('only-untraversable', denied, 1, None, True),
        ('launcher-shim-excluded', path('.codex/tmp/arg0/session')+':'+readable, 0, canonical[readable], False),
    ]
    results = []
    for name, value, code, expected, diagnostic in cases:
        # The denied path is a real directory, so the production -d predicate
        # succeeds. Only traversal is fault-injected, matching the Windows bug.
        script = ('set -eu\nDENIED='+quote(denied)+'\n'
                  'cd() { if [ "${2:-}" = "$DENIED" ]; then return 1; fi; builtin cd "$@"; }\n'
                  'PATH='+quote(value)+'\n'+block+'printf "RESULT:%s\\n" "$PATH"\n')
        f = args.output/(name+'.sh')
        f.write_bytes(script.encode('utf-8'))
        try:
            r = subprocess.run([shell, str(f)], capture_output=True, timeout=15)
            out, err = r.stdout.decode(), r.stderr.decode()
            assert r.returncode == code, (r.returncode, out, err)
            if expected is not None:
                assert out == 'RESULT:'+expected+'\n', out
            else:
                assert 'canonical bootstrap PATH is empty' in err, err
            assert ('skipping inaccessible bootstrap PATH directory: '+denied in err) == diagnostic, err
            results.append(dict(name=name, status='PASS'))
        except Exception as exc:
            results.append(dict(name=name, status='FAIL', error=str(exc)))
    data = dict(cases=results, passed=sum(x['status']=='PASS' for x in results), failed=sum(x['status']=='FAIL' for x in results), bootstrap_run=False, permission_model='existing directory with injected cd denial; no ACL elevation')
    (args.output/'result.json').write_text(json.dumps(data, indent=2), encoding='utf-8')
    print(json.dumps(data))
    return int(data['failed'] != 0)


if __name__ == '__main__':
    raise SystemExit(main())

"""Actual-helper regressions for streamed bootstrap Cargo path extraction.

--script authority.shs --output NEW_DIRECTORY [--snapshot CAPTURED_MANIFEST_ROOT]
No bootstrap/compiler invocation, source edits, privileged links or ACL changes.
"""
import argparse
import ctypes
import json
import pathlib
import subprocess


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--script', required=True, type=pathlib.Path)
    ap.add_argument('--output', required=True, type=pathlib.Path)
    ap.add_argument('--snapshot', type=pathlib.Path)
    ap.add_argument('--only', help='Run only this changed or previously failing case')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    src = args.script.read_text(encoding='utf8')
    start = src.index('bootstrap_stage3_cargo_path_pairs() {')
    end = src.index('\n}\n', start)+3
    helper = src[start:end]
    start = src.index('        while IFS= read -r bootstrap_stage3_seed_manifest_dir; do')
    end = src.index('        done <"$bootstrap_stage3_seed_tmp/path-dep-pairs"', start)
    validator = src[start:end]+'        done <"$bootstrap_stage3_seed_tmp/path-dep-pairs"\n'
    shell = 'C:/Program Files/Git/bin/bash.exe'
    rows = []

    def case(name, fn):
        if args.only and args.only != name:
            return
        try:
            rows.append(dict(name=name, status='PASS', detail=fn()))
        except Exception as exc:
            rows.append(dict(name=name, status='FAIL', error=str(exc)))

    def extract(name, files, manifests, expected, fail=False):
        root = args.output/name
        root.mkdir()
        for path, text in files.items():
            f = root/path
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_bytes(text.encode('utf8'))
        (root/'manifest-list').write_bytes(('\n'.join(manifests)+'\n').encode())
        (root/'run.sh').write_bytes((helper+'\nbootstrap_stage3_cargo_path_pairs manifest-list\n').encode())
        r = subprocess.run([shell, str(root/'run.sh')], cwd=root, capture_output=True, timeout=15)
        if fail:
            assert r.returncode != 0, r.stdout
        else:
            assert r.returncode == 0, r.stderr
            assert r.stdout == expected.encode(), (r.stdout, expected)
        return dict(exit_code=r.returncode, pairs=r.stdout.count(b'\n')//2)

    case('literal-spaces-and-origin', lambda: extract('spaces', {'a space/Cargo.toml':'[dependencies]\nx={path="../space dependency"}\n'}, ['a space/Cargo.toml'], 'a space\n../space dependency\n'))
    case('multiple-files-reset-section', lambda: extract('reset', {'one/Cargo.toml':'[dependencies]\nx={path="../dep"}\n', 'two/Cargo.toml':'[package]\npath="not-a-dependency"\n'}, ['one/Cargo.toml','two/Cargo.toml'], 'one\n../dep\n'))
    case('duplicate-order-preserved', lambda: extract('duplicates', {'a/Cargo.toml':'[dependencies]\nx={path="../x"}\ny={path="../y"}\n'}, ['a/Cargo.toml','a/Cargo.toml'], 'a\n../x\na\n../y\na\n../x\na\n../y\n'))
    case('root-manifest-origin', lambda: extract('root', {'Cargo.toml':'[dependencies]\nx={path="child"}\n'}, ['Cargo.toml'], '.\nchild\n'))
    headers = ['dependencies', 'build-dependencies', 'dependencies.foo', 'target.\'cfg(windows)\'.dependencies', 'workspace.dependencies', 'patch.crates-io', 'replace']
    case('supported-sections', lambda: extract('sections', {'a/Cargo.toml':''.join('['+h+']\nx={path="../d'+str(i)+'"}\n' for i,h in enumerate(headers))}, ['a/Cargo.toml'], ''.join('a\n../d'+str(i)+'\n' for i in range(len(headers)))))
    case('unrelated-sections-excluded', lambda: extract('excluded', {'a/Cargo.toml':'[package]\npath="ignored"\n[dev-dependencies]\nx={path="ignored-too"}\n'}, ['a/Cargo.toml'], ''))
    case('missing-manifest-fails', lambda: extract('missing', {}, ['absent/Cargo.toml'], '', fail=True))
    case('later-read-error-fails-after-partial-output', lambda: extract('partial', {'a/Cargo.toml':'[dependencies]\nx={path="../x"}\n'}, ['a/Cargo.toml','missing/Cargo.toml'], '', fail=True))
    case('literal-invalid-dependency-not-normalized', lambda: extract('literal', {'a/Cargo.toml':'[dependencies]\nx={path="../../outside"}\ny={path="C:/outside"}\n'}, ['a/Cargo.toml'], 'a\n../../outside\na\nC:/outside\n'))
    # Git for Windows awk reads these files in text mode. The actual original
    # parser also recognizes this CRLF header; do not infer a defect from the
    # anchored regex without executing the host's input conversion behavior.
    case('CRLF-old-parser-parity', lambda: extract('crlf', {'a/Cargo.toml':'[dependencies]\r\nx={path="../dep"}\r\n'}, ['a/Cargo.toml'], 'a\n../dep\n'))

    def validate_paths(name, dependency, expected):
        parent = args.output/name
        root = parent/'repo'
        for d in ('repo/src/compiler_rust', 'repo/src/runtime', 'repo/tmp', 'outside'):
            (parent/d).mkdir(parents=True, exist_ok=True)
        (root/'tmp/path-deps.unsorted').write_bytes(b'')
        (root/'tmp/path-dep-pairs').write_bytes(('src/compiler_rust\n'+dependency+'\n').encode())
        script = ('set -eu\nbootstrap_stage3_seed_root=$(pwd -P)\nbootstrap_stage3_seed_tmp=tmp\n'+validator)
        f = root/'validate.sh'; f.write_bytes(script.encode())
        r = subprocess.run([shell, str(f)], cwd=root, capture_output=True, timeout=15)
        assert (r.returncode == 0) == expected, (r.returncode, r.stderr)
        if expected:
            assert (root/'tmp/path-deps.unsorted').read_bytes() == b'src/runtime\n'
        return dict(exit_code=r.returncode)
    case('existing-validator-allows-contained-runtime', lambda: validate_paths('valid-dep','../runtime', True))
    case('existing-validator-rejects-escape', lambda: validate_paths('escape','../../../outside', False))
    case('existing-validator-rejects-missing', lambda: validate_paths('absent','../absent', False))

    if args.snapshot:
        def memory():
            class Counters(ctypes.Structure):
                _fields_ = [('cb',ctypes.c_ulong),('faults',ctypes.c_ulong)]+[(x,ctypes.c_size_t) for x in ('peak','working','pagepoolpeak','pagepool','nonpagepeak','nonpage','pagefile','peakpagefile')]
            query = ctypes.WinDLL('psapi').GetProcessMemoryInfo
            query.argtypes = [ctypes.c_void_p,ctypes.POINTER(Counters),ctypes.c_ulong]
            query.restype = ctypes.c_int
            program = helper.split("    awk '\n",1)[1].rsplit("    ' \"$1\"",1)[0]
            awk = args.output/'parser.awk'; awk.write_bytes(program.encode())
            data = (args.snapshot/'cargo-manifests').read_bytes()
            observations = []
            for multiplier in (1,8):
                listing = args.output/('resource-'+str(multiplier)+'.list'); listing.write_bytes(data*multiplier)
                with (args.output/('resource-'+str(multiplier)+'.pairs')).open('wb') as out:
                    proc = subprocess.Popen(['C:/Program Files/Git/usr/bin/awk.exe','-f',str(awk),str(listing)], cwd=args.snapshot, stdout=out, stderr=subprocess.PIPE)
                    _, err = proc.communicate(timeout=60)
                    assert proc.returncode == 0, err
                    counters = Counters(); counters.cb=ctypes.sizeof(counters)
                    assert query(int(proc._handle),ctypes.byref(counters),ctypes.sizeof(counters)), ctypes.get_last_error()
                    observations.append(dict(multiplier=multiplier,peak_rss=counters.peak))
            assert (args.output/'resource-8.pairs').read_bytes() == (args.output/'resource-1.pairs').read_bytes()*8
            assert observations[1]['peak_rss'] <= observations[0]['peak_rss']+8*1024*1024, observations
            return observations
        case('streaming-memory-eightfold-input', memory)
    result = dict(cases=rows, passed=sum(x['status']=='PASS' for x in rows), failed=sum(x['status']=='FAIL' for x in rows), bootstrap_run=False)
    (args.output/'result.json').write_text(json.dumps(result, indent=2), encoding='utf8')
    print(json.dumps(result))
    return int(result['failed'] != 0)


if __name__ == '__main__':
    raise SystemExit(main())

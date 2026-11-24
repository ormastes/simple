#!/usr/bin/env python3
"""Exercise the production COFF linker selector without rebuilding a seed.

Proves rooted COFF extraction and a final PE link, not execution on a foreign OS.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cc', required=True)
    p.add_argument('--ar', required=True)
    p.add_argument('--nm', required=True)
    p.add_argument('--readobj', required=True)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--retained-archive', type=Path)
    args = p.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[2]
    owner = root / 'src/compiler_rust/compiler/src/pipeline/native_project/coff_partial_link.rs'
    commands = []

    def run(argv, label, expected=0):
        result = subprocess.run([str(x) for x in argv], capture_output=True, timeout=60)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        commands.append(dict(argv=[str(x) for x in argv], label=label, exit=result.returncode))
        (out / 'commands.json').write_text(json.dumps(commands, indent=2), encoding='utf-8')
        if expected == 'failure':
            assert result.returncode != 0, label
        else:
            assert result.returncode == expected, (label, result.stderr.decode(errors='replace'))
        return result

    # Compile the actual production module, not a Python imitation of selection.
    harness = out / 'owner.rs'
    harness.write_text(
        '#[path=' + json.dumps(str(owner).replace('\\', '/')) + '] mod owner;\n'
        'fn main() { let a: Vec<String> = std::env::args().collect();\n'
        ' if a[1] == "scope-controls" {\n'
        '  assert!(owner::command(true, "aarch64").unwrap().is_none());\n'
        '  assert!(owner::command(false, "x86_64").unwrap().is_none()); return; }\n'
        ' let mut c = owner::command(true, &a[1]).expect("COFF owner selection").expect("x86 COFF override");\n'
        ' c.args(&a[2..]); eprintln!("{c:?}");\n'
        ' let s = c.status().expect("COFF owner execution");\n'
        ' std::process::exit(s.code().unwrap_or(125)); }\n', encoding='utf-8')
    executable = out / ('owner.exe' if os.name == 'nt' else 'owner')
    run(['rustc', '--edition=2021', harness, '-o', executable], 'build-owner')
    run([executable, 'scope-controls'], 'unchanged-target-paths')
    for name, source in {
        'root': 'extern int dependency(void); int fixture_root(void) { return dependency() + 1; }\n',
        'dependency': 'int dependency(void) { return 41; }\n',
        'main': 'extern int fixture_root(void); int main(void) { return fixture_root() == 42 ? 0 : 1; }\n',
    }.items():
        c = out / (name + '.c')
        c.write_text(source, encoding='utf-8')
        run([args.cc, '--target=x86_64-w64-windows-gnu', '-c', c, '-o', out / (name + '.o')], name)
    archive = out / 'fixture.a'
    run([args.ar, 'rcs', archive, out / 'root.o', out / 'dependency.o'], 'archive')
    run([args.cc, '--target=x86_64-w64-windows-gnu', '-fuse-ld=lld', '-nostdlib', '-Wl,-r',
         '-Wl,--undefined=fixture_root', archive, '-o', out / 'old-closure.o'], 'old-pe-lld', expected='failure')
    assert b'unknown argument: -r' in (out / 'old-pe-lld.stderr').read_bytes()
    closure = out / 'closure.o'
    run([executable, 'x86_64', '--undefined=fixture_root', '--start-group', archive, '--end-group', '-o', closure], 'coff-closure')
    header = run([args.readobj, '--file-headers', closure], 'coff-header').stdout
    assert b'COFF-x86-64' in header and b'IMAGE_FILE_MACHINE_AMD64' in header
    symbols = run([args.nm, '--defined-only', closure], 'roots').stdout.decode()
    for name in ['fixture_root', 'dependency']:
        assert sum(line.split()[-1:] == [name] for line in symbols.splitlines()) == 1, name
    undefined = run([args.nm, '--undefined-only', closure], 'undefined').stdout
    assert b'dependency' not in undefined
    pe = out / 'fixture.exe'
    run([args.cc, '--target=x86_64-w64-windows-gnu', '-fuse-ld=lld', '--rtlib=compiler-rt',
         '--unwindlib=libunwind', out / 'main.o', closure, '-o', pe], 'final-pe')
    pe_header = run([args.readobj, '--file-headers', pe], 'pe-header').stdout
    assert b'IMAGE_FILE_EXECUTABLE_IMAGE' in pe_header
    if args.retained_archive:
        retained = args.retained_archive.resolve()
        defined = run([args.nm, '--defined-only', retained], 'retained-roots').stdout.decode()
        assert sum(line.split()[-1:] == ['rt_file_exists'] for line in defined.splitlines()) == 1
        retained_closure = out / 'retained-closure.o'
        run([executable, 'x86_64', '--undefined=rt_file_exists', retained, '-o', retained_closure], 'retained-closure')
        defined = run([args.nm, '--defined-only', retained_closure], 'retained-result').stdout.decode()
        assert sum(line.split()[-1:] == ['rt_file_exists'] for line in defined.splitlines()) == 1
    files = [owner, harness, archive, closure, pe]
    if args.retained_archive: files.append(args.retained_archive.resolve())
    manifest = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
    (out / 'hashes.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')
    checks = ['non-x86-and-non-windows-gnu-paths-unchanged', 'old-pe-lld-rejected-relocatable', 'coff-amd64-format',
              'root-and-dependency-defined-once', 'dependency-resolved', 'final-clang-lld-pe-link']
    if args.retained_archive: checks.append('retained-runtime-root-extracted-once')
    (out / 'result.json').write_text(json.dumps(dict(status='PASS', checks=checks,
        qualification='production selector; rooted COFF closure; pinned Clang/LLD final PE link; no execution claim',
        retained_archive_checked=bool(args.retained_archive)), indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()

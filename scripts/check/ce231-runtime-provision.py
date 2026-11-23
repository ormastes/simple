"""Build and retain a new exact-source runtime tuple, without compiler promotion."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
source = Path('source').resolve()
root = Path('runtime-evidence').resolve()
root.mkdir(exist_ok=False)
payload = root / 'runtime'
payload.mkdir()
(payload / 'deps').mkdir()

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def capture(name, command, cwd=source):
    result = subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    (root / name).write_bytes(result.stdout)
    return result.stdout

assert capture('source-head.txt', ['git', 'rev-parse', 'HEAD']).decode().strip() == SOURCE
capture('source-clean.txt', ['git', 'diff', '--exit-code', 'HEAD'])
capture('source-tree.txt', ['git', 'ls-tree', '-r', '--full-tree', 'HEAD'])
toolchain = (source / 'src/compiler_rust/rust-toolchain.toml').read_text()
assert 'channel = "nightly-2026-09-15"' in toolchain
for name, command in [('rustc', ['rustc', '+nightly-2026-09-15', '-vV']),
                      ('cargo', ['cargo', '+nightly-2026-09-15', '-V']),
                      ('clang', ['clang', '--version']), ('lld', ['ld.lld', '--version']),
                      ('ar', ['llvm-ar', '--version']), ('nm', ['llvm-nm', '--version']),
                      ('cc', ['cc', '--version']), ('ld', ['ld', '--version']),
                      ('glibc', ['ldd', '--version'])]:
    capture(name + '.txt', command)
for name in ['rustc', 'cargo']:
    actual = capture(name + '-path.txt', ['rustup', 'which', '--toolchain', 'nightly-2026-09-15', name]).decode().strip()
    (root / (name + '-sha256.txt')).write_text(sha(Path(actual)) + '\n')

available = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))
cap = min(8 * 1024 * 1024, available * 3 // 4, available - 2 * 1024 * 1024)
assert cap >= 4 * 1024 * 1024, 'insufficient runtime build headroom'
env = {key: value for key, value in os.environ.items()
       if not key.startswith(('SIMPLE_', 'CARGO_', 'RUSTFLAGS', 'RUSTC_WRAPPER'))}
target = root / 'cargo-target'
env.update(CARGO_TARGET_DIR=str(target), CARGO_HOME=str(root / 'cargo-home'),
           TMPDIR=str(root / 'tmp'), CC=shutil.which('clang'), CXX=shutil.which('clang++'),
           AR=shutil.which('llvm-ar'))
for key in ['CARGO_HOME', 'TMPDIR']:
    Path(env[key]).mkdir()
profile = target / 'x86_64-unknown-linux-gnu/bootstrap'
commands = [
    ['-p', 'simple-native-all', '-p', 'spl_hosted_runtime', '--features', 'simple-native-all/driver-compat'],
    ['-p', 'simple-runtime', '--features', 'runtime-symbol-table'],
    ['-p', 'simple-compiler-backfill'],
]
base = ['cargo', '+nightly-2026-09-15', 'build', '--locked', '--offline', '--profile', 'bootstrap',
        '--target', 'x86_64-unknown-linux-gnu', '--jobs', '2']
# One finite owner contains every Cargo child and all three sequential invocations.
runner = root / 'build.sh'
import shlex
lines = ['set -eu']
for index, args in enumerate(commands):
    lines.append(('CARGO_PROFILE_BOOTSTRAP_LTO=off ' if index == 1 else '') + shlex.join(base + args))
    name = ['libsimple_native_all.a', 'libsimple_runtime.a', 'libsimple_compiler_backfill.a'][index]
    lines.append(shlex.join(['cp', str(profile / name), str(payload / name)]))
    if index == 0:
        selected = shlex.quote(str(profile / 'libspl_hosted_runtime.rlib'))
        lines += [f'if [ -f {selected} ]; then',
                  shlex.join(['cp', str(profile / 'libspl_hosted_runtime.rlib'), str(payload / 'deps/libspl_hosted_runtime.rlib')]),
                  'else', f'set -- {shlex.quote(str(profile / "deps"))}/libspl_hosted_runtime*.rlib',
                  '[ "$#" -eq 1 ] && [ -f "$1" ]',
                  'cp "$1" ' + shlex.quote(str(payload / 'deps')) + '/', 'fi']
runner.write_text('\n'.join(lines) + '\n')
owner = ['perl', str(source / 'scripts/resource/process-tree-rss-watchdog.pl'),
         '--rss-cap-mode=enforce', f'--max-rss-kib={cap}', '--timeout-seconds=1800',
         '--receipt=' + str(root / 'build.owner.env'), '--', 'bash', str(runner)]
manifest = {'status': 'FAILED', 'source_revision': SOURCE, 'target': 'x86_64-unknown-linux-gnu',
            'profile': 'bootstrap', 'commands': [base + args for args in commands],
            'runtime_nolto_override': {'command_index': 1, 'CARGO_PROFILE_BOOTSTRAP_LTO': 'off'},
            'owner_argv': owner, 'rss_cap_kib': cap, 'available_kib': available,
            'admission': 'none', 'scope': 'new same-source runtime bytes; not the original Phase2 link input',
            'source_tree_manifest_sha256': sha(root / 'source-tree.txt'),
            'cargo_lock_sha256': sha(source / 'src/compiler_rust/Cargo.lock'),
            'cargo_config_sha256': sha(source / 'src/compiler_rust/.cargo/config.toml'),
            'toolchain_file_sha256': sha(source / 'src/compiler_rust/rust-toolchain.toml'),
            'tools': {name: {'path': env[name], 'sha256': sha(Path(env[name]))} for name in ['CC', 'CXX', 'AR']}}
manifest['rust_default_link_tools'] = {
    name: {'path': shutil.which(name), 'sha256': sha(Path(shutil.which(name)))} for name in ['cc', 'ld']}
manifest['link_tool_scope'] = 'CC/CXX/AR bind build-script tools; rustc default cc/ld resolved separately; no claim every link used clang/LLD'
try:
    with (root / 'build.stdout').open('wb') as out, (root / 'build.stderr').open('wb') as err:
        code = subprocess.run(owner, cwd=source / 'src/compiler_rust', env=env, stdout=out, stderr=err).returncode
    receipt = dict(line.split('=', 1) for line in (root / 'build.owner.env').read_text().splitlines() if '=' in line)
    assert code == 0 and receipt['status'] == 'complete' and receipt['exit_status'] == '0', receipt
    assert receipt['quiescent'] == '1' and receipt['rss_cap_enforced'] == '1'
    assert int(receipt.get('rss_limit_kib', receipt.get('max_rss_kib', '0'))) == cap
    for name in ['libsimple_native_all.a', 'libsimple_runtime.a', 'libsimple_compiler_backfill.a']:
        capture(name + '.members.txt', ['llvm-ar', 't', str(payload / name)])
        # The distribution's LLVM tools can be older than rustc's LTO bitcode.
        # Retain an honest inventory result; native link/ABI admission is separate.
        with (root / (name + '.symbols.txt')).open('wb') as inventory:
            inspection = subprocess.run(['llvm-nm', '--defined-only', str(payload / name)],
                                        stdout=inventory, stderr=subprocess.STDOUT)
        manifest.setdefault('symbol_inspection_exit', {})[name] = inspection.returncode
    assert len(list((payload / 'deps').glob('libspl_hosted_runtime*.rlib'))) == 1
    capture('source-clean-after.txt', ['git', 'diff', '--exit-code', 'HEAD'])
    manifest['files'] = {str(path.relative_to(payload)): {'sha256': sha(path), 'bytes': path.stat().st_size}
                         for path in payload.rglob('*') if path.is_file()}
    manifest.update(status='BUILT_UNQUALIFIED', native_hello='UNRUN', parent_binding='UNRUN')
finally:
    (root / 'manifest.json').write_text(json.dumps(manifest, indent=2))

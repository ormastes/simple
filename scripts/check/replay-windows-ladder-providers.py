#!/usr/bin/env python3
"""Replay the retained 45211128098 Windows link, never its 1612-file compile.

The immutable incident archive is a regression fixture, not a release input.
Outputs remain provisional even after the separate native Hello succeeds.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

REVISION = '68bb1b5d22340f9f730d37e584033793a821f0ce'
SEED_SHA = '116ca28bf3d5e8215e52391e5abdde14f2ced9d9c0e1102038cb36922224495d'
RUNTIME_SHA = 'c71c014449d81f74f7c3f181e64ca5c4bc7a751ec9199899982ee2ce44c9d03b'


def digest(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def quoted(line):
    return [json.loads(token).removeprefix('\\\\?\\')
            for token in re.findall(r'"(?:\\.|[^"\\])*"', line)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('fixture', 'source', 'toolchain', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    fixture, source, toolchain, out = [getattr(args, name).resolve()
                                     for name in ('fixture', 'source', 'toolchain', 'output')]
    root = Path(__file__).resolve().parents[2]
    out.mkdir(parents=True, exist_ok=False)
    seed = fixture/'producer/simple.exe'
    runtime = fixture/'producer/runtime/libsimple_native_all.a'
    if digest(seed) != SEED_SHA or digest(runtime) != RUNTIME_SHA:
        raise RuntimeError('incident producer/runtime identity mismatch')
    if (fixture/'evidence/source-revision.txt').read_text().strip() != REVISION:
        raise RuntimeError('incident source identity mismatch')
    if subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() != REVISION:
        raise RuntimeError('canonical supplement source must match incident')
    env = dict(os.environ, PATH=str(toolchain/'bin') + os.pathsep + os.environ['PATH'],
               CC=str(toolchain/'bin/clang.exe'), SIMPLE_WINDOWS_ABI='gnu',
               SIMPLE_LINKER_FLAVOR='gnu', SIMPLE_NATIVE_BUILD_RUST='1',
               SIMPLE_BOOTSTRAP='1', SIMPLE_NO_STUB_FALLBACK='1',
               SIMPLE_HOME=str(source), SIMPLE_LIB=str(source/'src'),
               TMP=str(out), TEMP=str(out))

    def command(argv, name, expected=0, timeout=300):
        argv = list(map(str, argv))
        (out/(name+'.argv.json')).write_text(json.dumps(argv, indent=2))
        with (out/(name+'.log')).open('wb') as log:
            result = subprocess.run(argv, cwd=source, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        (out/(name+'.exit')).write_text(str(result.returncode)+'\n')
        if (result.returncode == 0) != (expected == 0):
            raise RuntimeError(f'{name}: unexpected exit {result.returncode}; see log')
        return (out/(name+'.log')).read_text(errors='replace')

    # A strict missing extern deliberately retains the canonical supplement and
    # owner-member selection. It compiles one tiny file, not the compiler closure.
    probe = out/'probe'
    probe.mkdir()
    entry = probe/'bootstrap_main.spl'
    entry.write_text('extern fn missing_provider_probe_v1() -> i64\nfn main():\n    print missing_provider_probe_v1()\n')
    common = [seed, 'native-build', '--target', 'x86_64-pc-windows-gnu',
              '--backend', 'cranelift', '--threads', '1', '--verbose',
              '--runtime-bundle', 'core-c-bootstrap', '--runtime-path', runtime.parent]
    log = command(common + ['--source', probe, '--entry', entry, '--entry-closure',
                  '--cache-dir', out/'probe-cache', '--output', out/'negative.exe'],
                  'canonical-provider-probe', expected=1)
    if 'undefined symbol: missing_provider_probe_v1' not in log:
        raise RuntimeError('provider probe failed before its intended unresolved-symbol boundary')
    link = quoted(next(line for line in log.splitlines() if line.startswith('Link command:')))
    # Compile the unchanged production Simple owner in isolation for the ABI
    # regression. No test stand-in implements the thirteen exports.
    pure = out/'pure-source'
    pure.mkdir()
    shutil.copyfile(source/'src/lib/common/time_utils.spl', pure/'time_utils.spl')
    before = set(out.glob('native-objects-*'))
    command(common + ['--source', pure, '--entry', pure/'time_utils.spl',
            '--emit-object', '--cache-dir', out/'pure-cache', '--output', out/'pure.exe'],
            'production-simple-owner', expected=1)
    objects = list((set(out.glob('native-objects-*')) - before))
    if len(objects) != 1 or not (objects[0]/'mod_0.o').is_file():
        raise RuntimeError('expected exactly one retained real Simple owner object')
    regression = out/'provider-regression'
    command([sys.executable, root/'scripts/check/check-windows-timestamp-providers.py',
             '--toolchain', toolchain, '--runtime-archive', runtime,
             '--simple-object', objects[0]/'mod_0.o', '--producer', seed,
             '--output', regression], 'provider-controls')
    retained = fixture/'cache/native-objects-iX0DnB'
    owner_arg = next(arg for arg in link if arg.startswith('@') and arg.endswith('native_all_owner_members.rsp'))
    owners = quoted(Path(owner_arg[1:]).read_text())
    patched_member = next(regression.glob('*-runtime_timestamp.o'))
    original_member = Path(owner_arg[1:]).parent/'native_all_owner_members'/patched_member.name
    old_sha = digest(original_member)
    matching = [index for index, path in enumerate(owners) if digest(path) == old_sha]
    if len(matching) != 1:
        raise RuntimeError('expected exactly one timestamp owner member')
    owners[matching[0]] = str(patched_member)
    response = out/'fixed-owner-members.rsp'
    response.write_text(' '.join(json.dumps(path) for path in owners)+'\n')
    for index, arg in enumerate(link):
        for name in ('_main_stub.o', '_init_all.o', '_stubs.o'):
            if arg.endswith(name):
                link[index] = str(retained/name)
        if arg.endswith('mod_0.o'):
            link[index] = str(retained/'libspl_objects.a')
        elif arg.endswith('libsimple_native_all.a'):
            link[index] = str(regression/'libsimple_native_all.a')
        elif arg == owner_arg:
            link[index] = '@'+str(response)
    candidate = out/'simple.exe'
    link[link.index('-o')+1] = str(candidate)
    command(link, 'retained-compiler-link')
    command([candidate, '--version'], 'candidate-version', timeout=30)
    paths = [seed, runtime, retained/'libspl_objects.a', candidate, patched_member,
             regression/'libsimple_native_all.a']
    paths += [Path(arg) for arg in link if Path(arg).is_file()]
    (out/'link-identities.json').write_text(json.dumps({str(path): digest(path) for path in paths}, indent=2))
    # Match the ladder's distinct candidate-native Hello gate. Rust seed routing
    # must not stand in for running this newly linked Simple compiler.
    env.pop('SIMPLE_NATIVE_BUILD_RUST', None)
    env['SIMPLE_BOOTSTRAP_WHOLE_PROGRAM'] = '1'
    # The candidate's source-closure validator requires the entry in its caller
    # checkout. Generated build inputs do not modify any tracked incident bytes.
    hello_dir = source/'build/retained-provider-hello'
    hello_dir.mkdir(parents=True, exist_ok=False)
    hello = hello_dir/'hello.spl'
    hello.write_text('fn main():\n    print "retained-ladder-hello-ok"\n')
    command([candidate, 'native-build', hello, '-o', out/'hello.exe'], 'candidate-native-hello', timeout=900)
    stdout = command([out/'hello.exe'], 'hello-run', timeout=30)
    if stdout.strip() != 'retained-ladder-hello-ok':
        raise RuntimeError('native Hello output mismatch')
    (out/'PASS.json').write_text(json.dumps({'status': 'diagnostic-hello-pass',
        'admission': 'none', 'source': REVISION, 'candidate_sha256': digest(candidate),
        'hello_sha256': digest(out/'hello.exe')}, indent=2))
    print('PASS: retained compiler links, starts, compiles native Hello, and executes exact output')


if __name__ == '__main__':
    main()

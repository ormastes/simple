"""Bounded actual focused dispatcher proof; no compiler-generation admission."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import traceback

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('intake', HERE / 'proof.py')
n = importlib.util.module_from_spec(spec)
spec.loader.exec_module(n)
SOURCE = 'cefb9bdb94aa94c53aac1c02673d8eaab30e0843'
n.OUT = n.ROOT / 'build/focused-output-proof'
n.OUT.mkdir(parents=True, exist_ok=False)


def main():
    assert sys.platform == 'win32'
    compiler, bundle = n.intake(SOURCE)
    tools = n.toolchain()
    llvm = n.provider()
    assert n.sha(compiler) == 'f8be04ff2979d4b41cd038f8aa3601619891ec7cf74b55dbe73f06c84baa85f0'
    env = {k: v for k, v in os.environ.items() if not k.startswith('SIMPLE_')}
    env.update(PATH=';'.join([str(llvm), str(tools), str(n.BASH.parent.parent / 'usr/bin'),
                             str(n.BASH.parent.parent / 'mingw64/bin'), env['PATH']]),
               CC=str(tools / 'clang.exe'), CXX=str(tools / 'clang++.exe'),
               SIMPLE_MINGW_ROOT=n.posix(tools.parent), SIMPLE_WINDOWS_ABI='gnu',
               SIMPLE_NO_STUB_FALLBACK='1', SIMPLE_RUNTIME_PATH=str(bundle),
               SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1', SIMPLE_SCV_INVENTORY_COLD_INIT='1',
               SIMPLE_KEEP_TEMP='1', SIMPLE_KERNEL_K1_POLICY='llvm',
               SIMPLE_PROJECT_ROOT=str(n.ROOT), SIMPLE_LIB=str(n.ROOT / 'src'),
               SIMPLE_FRONTEND_CACHE_DIR=str(n.OUT / 'cache/frontend'),
               SIMPLE_HIR_CACHE_DIR=str(n.OUT / 'cache/hir'))
    imports = n.command([tools / 'llvm-readobj.exe', '--coff-imports', compiler],
                        capture_output=True, text=True).stdout
    if 'libLLVM-23.dll' in imports:
        n.command([n.BASH, n.ROOT / 'scripts/setup/bundle-llvm-runtime-dlls.shs',
                   n.posix(compiler), n.posix(llvm)], env=env)
    tracked = n.command(['git', 'ls-files', '-z'], capture_output=True).stdout.decode().split('\0')
    source = {p: n.sha(n.ROOT / p) for p in tracked if p and (n.ROOT / p).is_file()}
    inputs = {str(p.relative_to(n.OUT)): n.sha(p)
              for base in (compiler.parent, bundle, tools, llvm)
              for p in base.rglob('*') if p.is_file()}
    n.save('source-files.json', source)
    n.save('inputs.json', {'source': SOURCE, 'parent_source': n.SOURCE,
                          'parent_sha256': n.sha(compiler), 'files': inputs,
                          'binding': n.BINDING, 'control': os.environ['GITHUB_SHA']})
    # The dispatcher and every runtime-search ancestor are outside the checkout.
    isolated = Path(os.environ['RUNNER_TEMP']) / ('focused-output-' + os.environ['GITHUB_RUN_ID'])
    isolated.mkdir(exist_ok=False)
    for parent in (isolated, *isolated.parents):
        assert not (parent / 'src/runtime/runtime.c').exists()
    product = isolated / 'focused-dispatcher.exe'
    cap = n.budget()
    n.save('compile-resource.json', json.loads((n.OUT / 'resource.json').read_text()))
    argv = [str(compiler), 'native-build', '--backend', 'llvm', '--target',
            'x86_64-pc-windows-gnu', '--runtime-bundle', 'core-c-bootstrap',
            '--runtime-path', str(bundle), '--threads', '1', '--entry-closure',
            '--mode', 'one-binary']
    for root in ('src/compositions/kernel_llvm', 'src/compositions/cuda_static',
                 'src/compiler', 'src/app', 'src/lib', 'src/plugins'):
        argv.extend(['--source', root])
    argv.extend(['--entry', 'test/fixtures/bootstrap_focused_output/dispatcher.spl',
                 '--cache-dir', str(n.OUT / 'cache'), '--output', str(product)])
    try:
        n.owned('compile', argv, cap, 1800, env)
        assert product.is_file()
        digest = n.sha(product)
        pe = n.command([tools / 'llvm-readobj.exe', '--coff-imports', product],
                       capture_output=True, text=True).stdout
        (n.OUT / 'dispatcher.imports').write_text(pe)
        assert 'COFF-x86-64' in pe
        # Use the existing hash-bound tool/provider PATH; do not add fake imports.
        n.owned('cases', [sys.executable, str(n.ROOT / 'scripts/check/check-focused-native-output.py'),
                         '--dispatcher', str(product), '--output', str(isolated / 'cases')],
                min(cap, 2 * 1024 * 1024), 600, env)
        result = json.loads((isolated / 'cases/result.json').read_text())
        assert result['status'] == 'PASS' and len(result['cases']) == 4
        assert result['dispatcher_sha256'] == digest == n.sha(product)
        terminal = {'status': 'ACTUAL_FOCUSED_OUTPUT_PASS', 'source': SOURCE,
                    'dispatcher_sha256': digest, 'cases': result,
                    'scope': 'actual focused owner; not Phase3 or Hello qualification'}
    finally:
        if product.exists():
            shutil.copy2(product, n.OUT / product.name)
        if (isolated / 'cases').exists():
            shutil.copytree(isolated / 'cases', n.OUT / 'cases')
        unchanged = (all(n.sha(n.ROOT / p) == h for p, h in source.items()) and
                     all(n.sha(n.OUT / p) == h for p, h in inputs.items()))
        n.save('immutable-inputs.json', {'unchanged': unchanged})
        assert unchanged
    n.save('terminal.json', terminal)


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        n.save('failure.json', {'error': str(error), 'traceback': traceback.format_exc()})
        raise

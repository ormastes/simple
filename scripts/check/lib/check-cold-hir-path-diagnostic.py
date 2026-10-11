"""Compile an exact extracted production diagnostic and verify all output lines."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import textwrap

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def expected_output():
    rows = []
    for case in ('empty-map', 'missing-name', 'empty-names', 'present-name', 'empty-sources'):
        rows.append('CASE ' + case)
        if case != 'empty-sources':
            hir = '/other/main.spl' if case == 'present-name' else ''
            rows.append("cold HIR path evidence: root='/frozen' source='/other/main.spl' hir='" + hir + "'")
        rows.extend(['cold HIR receipt capture failed: cold-hir-module-source-mismatch', 'CASE_DONE ' + case])
    return rows + ['NATIVE_DIAGNOSTIC_CASES_COMPLETED 5']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source-root', 'producer', 'runtime', 'shell', 'output', 'target'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--backend', choices=('llvm', 'cranelift'), required=True)
    parser.add_argument('--producer-kind', choices=('self-hosted', 'bootstrap-diagnostic'), required=True)
    parser.add_argument('--compile-timeout', type=int, default=600)
    parser.add_argument('--run-timeout', type=int, default=30)
    args = parser.parse_args()
    if min(args.compile_timeout, args.run_timeout) < 1:
        parser.error('positive timeout required')
    paths = {}
    for name in ('source_root', 'producer', 'runtime', 'shell'):
        path = Path(getattr(args, name))
        if not path.is_absolute() or path.is_symlink():
            parser.error(name + ' must be an absolute non-symlink path')
        paths[name] = path.resolve(strict=True)
    source = paths['source_root'] / 'src/compiler/80.driver/driver_hir_pipeline_lowering.spl'
    watchdog = paths['source_root'] / 'scripts/bootstrap/run-process-group-timeout.shs'
    if not paths['runtime'].is_dir() or not all(p.is_file() for p in (source, watchdog, paths['producer'], paths['shell'])):
        parser.error('missing source/watchdog/producer/shell/runtime input')
    output = Path(args.output)
    if not output.is_absolute() or output.exists() or output.is_symlink():
        parser.error('output must be a fresh absolute path')
    output = output.parent.resolve(strict=True) / output.name
    for protected in (paths['source_root'], paths['runtime']):
        if output.is_relative_to(protected) or protected.is_relative_to(output):
            parser.error('output overlaps protected source/runtime')
    original = source.read_bytes()
    text = original.decode()
    begin_marker = '                        if reason == "cold-hir-module-source-mismatch"'
    if text.count(begin_marker) != 1:
        raise ValueError('production extraction start is not unique')
    begin = text.index(begin_marker)
    end = text.index('                    case Ok(receipts):', begin)
    block = textwrap.dedent(text[begin:end])
    if 'return false' not in block or 'cold HIR receipt capture failed: {reason}' not in block:
        raise ValueError('production diagnostic extraction boundary changed')
    template = json.loads(Path(__file__).with_name('cold-hir-path-diagnostic-template.json').read_text())
    fixture = template['prefix'] + textwrap.indent(block, '        ') + template['suffix']
    output.mkdir()
    for child in ('src', 'tmp', 'cache'):
        (output / child).mkdir()
    (output / 'src/main.spl').write_text(fixture)
    # Real SCV admission needs a real source inventory, even for this tiny fixture.
    setup_env = os.environ.copy()
    for name in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES'):
        setup_env.pop(name, None)
    git = ['git', '-c', 'user.name=Diagnostic', '-c', 'user.email=diagnostic@localhost',
           '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null']
    with (output / 'setup.log').open('wb') as log:
        for command in (['init'], ['add', 'src/main.spl'], ['commit', '-m', 'Record diagnostic fixture']):
            subprocess.run(git + command, cwd=output, env=setup_env, stdout=log, stderr=log, check=True, timeout=30)
    environment = setup_env.copy()
    for name in list(environment):
        if name.startswith('SIMPLE_SCV_') or name in ('SIMPLE_BINARY', 'SIMPLE_BIN', 'SIMPLE_LIB', 'SIMPLE_RUNTIME_PATH', 'SIMPLE_BOOTSTRAP_SESSION_ID', 'SIMPLE_BOOTSTRAP_SESSION_EXEC'):
            environment.pop(name)
    for name in ('TMP', 'TEMP', 'TMPDIR'):
        environment[name] = str(output / 'tmp')
    for name, suffix in (('SIMPLE_NATIVE_BUILD_CACHE_DIR', ''), ('SIMPLE_FRONTEND_CACHE_DIR', 'frontend'), ('SIMPLE_HIR_CACHE_DIR', 'hir'), ('SIMPLE_RT_OBJ_CACHE_DIR', 'runtime')):
        environment[name] = str(output / 'cache' / suffix)
    environment.update(SIMPLE_PROJECT_ROOT=str(paths['source_root']), SIMPLE_SCV_INVENTORY_COLD_INIT='1', SIMPLE_NO_STUB_FALLBACK='1')
    exe = output / ('probe.exe' if 'windows' in args.target else 'probe')
    commands = [
        [str(paths['producer']), 'native-build', '--backend', args.backend, '--target', args.target,
         '--runtime-bundle', 'core-c-bootstrap', '--runtime-path', str(paths['runtime']),
         '--source', 'src', '--entry-closure', '--entry', 'src/main.spl', '--threads', '1',
         '--cache-dir', str(output / 'cache'), '--output', str(exe)],
        [str(exe)],
    ]
    receipt = dict(schema='cold-hir-path-diagnostic-v1', scope='diagnostic-only-not-admission',
                   producer_kind=args.producer_kind, producer=str(paths['producer']),
                   producer_sha256=digest(paths['producer']), production_source=str(source),
                   production_sha256=hashlib.sha256(original).hexdigest(),
                   block_sha256=hashlib.sha256(block.encode()).hexdigest(),
                   fixture_sha256=digest(output / 'src/main.spl'), backend=args.backend,
                   runtime=str(paths['runtime']), target=args.target, commands=commands, status='FAIL')
    for index, (name, timeout) in enumerate((('compile', args.compile_timeout), ('run', args.run_timeout))):
        with (output / (name + '.log')).open('wb') as log:
            result = subprocess.run([str(paths['shell']), str(watchdog), str(timeout), '5'] + commands[index],
                                    cwd=output, env=environment, stdout=log, stderr=log)
        receipt[name + '_exit'] = result.returncode
        if result.returncode:
            break
    if receipt.get('run_exit') == 0:
        actual = (output / 'run.log').read_text().splitlines()
        expected = expected_output()
        receipt.update(expected_lines=expected, actual_lines=actual,
                       source_unchanged=digest(source) == receipt['production_sha256'],
                       producer_unchanged=digest(paths['producer']) == receipt['producer_sha256'])
        if actual == expected and receipt['source_unchanged'] and receipt['producer_unchanged']:
            receipt['status'] = 'PASS'
    (output / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status=receipt['status'], evidence=str(output / 'result.json'), scope=receipt['scope'])))
    return 0 if receipt['status'] == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())

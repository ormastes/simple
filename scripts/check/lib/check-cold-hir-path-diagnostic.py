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
        if case == 'empty-sources':
            rows.append('cold HIR path evidence: no mismatched lowered source located')
        else:
            hir = '/other/main.spl' if case == 'present-name' else ''
            name = '' if case == 'empty-names' else 'pkg.main'
            rows.append("cold HIR path evidence: index=0 root='/frozen' source='/other/main.spl' module='" + name + "' hir='" + hir + "'")
        rows.extend(['cold HIR receipt capture failed: cold-hir-module-source-mismatch', 'CASE_DONE ' + case])
    return rows + ['NATIVE_DIAGNOSTIC_CASES_COMPLETED 5']

def extract_fixture(driver_text, helper_text, template):
    begin_marker = '                        if reason == "cold-hir-module-source-mismatch"'
    end_marker = '                    case Ok(receipts):'
    helper_begin = 'fn cold_hir_source_mismatch_evidence_v1('
    helper_end = '\nfn _cold_hir_source_path_error_v1('
    if driver_text.count(begin_marker) != 1 or driver_text.count(end_marker) != 1:
        raise ValueError('production diagnostic extraction boundaries are not unique')
    begin = driver_text.index(begin_marker)
    end = driver_text.index(end_marker, begin)
    block = textwrap.dedent(driver_text[begin:end])
    if ('return false' not in block or 'cold HIR receipt capture failed: {reason}' not in block
            or 'self.ctx.add_error(cold_hir_source_mismatch_evidence_v1(' not in block):
        raise ValueError('production diagnostic extraction boundary changed')
    if helper_text.count(helper_begin) != 1 or helper_text.count(helper_end) != 1:
        raise ValueError('production helper extraction boundaries are not unique')
    begin = helper_text.index(helper_begin)
    end = helper_text.index(helper_end, begin)
    helper = helper_text[begin:end]
    marker = '{{production_helper}}'
    if template['prefix'].count(marker) != 1 or marker in template['suffix']:
        raise ValueError('production helper insertion point is not unique')
    # Retain the production helper verbatim, including its HirModule signature.
    # The fixture supplies only the path/name fields this diagnostic reads.
    fixture = template['prefix'].replace(marker, helper)
    fixture += textwrap.indent(block, '        ') + template['suffix']
    return block, helper, fixture

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
    helper_source = paths['source_root'] / 'src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl'
    watchdog = paths['source_root'] / 'scripts/bootstrap/run-process-group-timeout.shs'
    if not paths['runtime'].is_dir() or not all(p.is_file() for p in (source, helper_source, watchdog, paths['producer'], paths['shell'])):
        parser.error('missing source/watchdog/producer/shell/runtime input')
    output = Path(args.output)
    if not output.is_absolute() or output.exists() or output.is_symlink():
        parser.error('output must be a fresh absolute path')
    output = output.parent.resolve(strict=True) / output.name
    for protected in (paths['source_root'], paths['runtime']):
        if output.is_relative_to(protected) or protected.is_relative_to(output):
            parser.error('output overlaps protected source/runtime')
    original = source.read_bytes()
    helper_original = helper_source.read_bytes()
    template_path = Path(__file__).with_name('cold-hir-path-diagnostic-template.json')
    template_original = template_path.read_bytes()
    block, helper, fixture = extract_fixture(original.decode(), helper_original.decode(),
                                             json.loads(template_original))
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
                   helper_source=str(helper_source),
                   helper_source_sha256=hashlib.sha256(helper_original).hexdigest(),
                   helper_block_sha256=hashlib.sha256(helper.encode()).hexdigest(),
                   template_sha256=hashlib.sha256(template_original).hexdigest(),
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
                       helper_unchanged=digest(helper_source) == receipt['helper_source_sha256'],
                       template_unchanged=digest(template_path) == receipt['template_sha256'],
                       producer_unchanged=digest(paths['producer']) == receipt['producer_sha256'])
        if (actual == expected and receipt['source_unchanged'] and receipt['helper_unchanged']
                and receipt['template_unchanged'] and receipt['producer_unchanged']):
            receipt['status'] = 'PASS'
    (output / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status=receipt['status'], evidence=str(output / 'result.json'), scope=receipt['scope'])))
    return 0 if receipt['status'] == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())

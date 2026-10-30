#!/usr/bin/env python3
"""Synthetic validator contract tests; no compiler/runtime/native artifact runs."""
import hashlib
import importlib.util
import json
import os
import stat
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('manual', ROOT/'scripts/check/lib/stage4-retained-manual.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class Contract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='manual-contract-')
        self.root = Path(self.tmp.name)
        # Tiny synthetic headers have no real symbol table. This explicit
        # metadata stub tests the verifier joins without executing any fixture.
        self.nm = patch.object(m, 'symbols', return_value=(
            {'___simple_main': True, '___module_init_fixture': True}, set(), 'synthetic nm metadata'))
        self.nm.start()

    def tearDown(self):
        self.nm.stop()
        self.tmp.cleanup()

    def text(self, name, text):
        p = self.root/name
        p.write_text(text)
        return p

    def header(self, name, kind):
        p = self.root/name
        p.write_bytes(struct.pack('<IIIIIIII', 0xfeedfacf, 0x100000c, 0, kind, 0, 0, 0, 0))
        p.chmod(0o700)
        return p

    def receipt(self, name, data):
        p = self.root/name
        m.write_env(p, data)
        return p

    def input_manifest(self, name, paths):
        return self.text(name, ''.join(m.sha(p)+'|'+str(p)+'\n' for p in dict.fromkeys(paths)))

    def transcript(self, name, binary, args, settings=()):
        rows = [('cwd', str(self.root)), ('executable', str(binary)), *[('argv', str(x)) for x in args], *[('explicit-env', str(x)) for x in settings]]
        return self.text(name, 'schema=simple-bootstrap-command-transcript-v2\n'+''.join(
            k+':'+str(len(v.encode()))+':'+v+'\n' for k, v in rows))

    def rss(self, name, raw):
        return self.receipt(name, {'status': 'complete', 'exit_status': raw, 'quiescent': 1,
             'rss_cap_mode': 'enforce', 'rss_cap_enforced': 1, 'observer_errors': 0, 'observer_restarts': 0,
             'measurement_budget_complete': 1, 'sample_budget_exceeded': 0, 'max_rss_kib': 3145728})

    def product_fixture(self, raw='1', response=False):
        # These byte headers/receipts are synthetic admission fixtures. They are
        # never executed or published as build/runtime qualification evidence.
        obj = self.header('aggregate.o', 1); artifact = self.header('artifact', 2)
        producer = self.header('producer', 2); cc = self.text('clang-pin', 'synthetic pinned tool')
        log, _ = self.log(raw)
        build_t = self.transcript('build.transcript', producer, ['native-build', '--entry', 'entry.spl',
             '--runtime-path', '/retained/runtime', '--mode', 'dynload', '--emit-object', '-o', str(obj)],
             ['SIMPLE_BINARY='+str(producer), 'SIMPLE_RUNTIME_PATH=/retained/runtime', 'SIMPLE_NO_STUB_FALLBACK=1'])
        build_rss = self.rss('build.rss.env', raw)
        q_inputs = self.input_manifest('qualification-inputs', [obj, log, build_t, build_rss])
        qualification = self.receipt('qualification.env', {'schema': 'simple-retained-object-qualification-v1',
             'artifact_path': obj, 'artifact_sha256': m.sha(obj), 'artifact_validation': 'PASS',
             'coordinator_raw_status': raw, 'normal_build_qualification': 'NOT_QUALIFIED',
             'evidence_manifest_path': q_inputs, 'evidence_manifest_sha256': m.sha(q_inputs)})
        c_objects = [self.header('runtime-'+str(i)+'.o', 1) for i in range(39)]
        c_manifest = self.input_manifest('retained-c.manifest', c_objects)
        nm = self.text('nm-pin', 'synthetic pinned symbol reader')
        template = self.text('entry-template.spl', '    var c_source = ""\n    c_source = c_source + "int main(int argc, char** argv) {return 0;}\\n"\n    file_write(entry_c, c_source)\n')
        init = self.text('module-init.txt', '__module_init_fixture\n')
        shim_source = self.text('entry.c', m.canonical_shim(template, ['__module_init_fixture']))
        shim_object = self.header('entry.o', 1)
        sdk = self.root/'sdk'; sdk.mkdir()
        sdk_settings = self.text('sdk/SDKSettings.plist', 'synthetic SDK pin')
        config = {'sdk_path': str(sdk)}
        for key, path in {'cc': cc, 'nm': nm, 'entry_template': template, 'sdk_settings': sdk_settings}.items():
            config[key+'_path'], config[key+'_sha256'] = str(path), m.sha(path)
        toolchain = self.receipt('toolchain.env', config)
        common = ['--target=aarch64-apple-darwin', '-mmacosx-version-min=26.5', '-isysroot', str(sdk)]
        shim_args = ['-c', *common, '-fPIC', '-O2', '-ffunction-sections', '-fdata-sections', '-o', str(shim_object), str(shim_source)]
        link_args = [str(obj), *map(str, c_objects), str(shim_object), *common,
             '-Wl,-dead_strip', '-Wl,-undefined,error', '-o', str(artifact)]
        extra_inputs = []
        if response:
            shim_response = self.text('shim.args', ''.join(json.dumps(x)+'\n' for x in shim_args))
            link_response = self.text('link.args', ''.join(json.dumps(x)+'\n' for x in link_args))
            extra_inputs = [shim_response, link_response]
            shim_args, link_args = ['@'+str(shim_response)], ['@'+str(link_response)]
        linked = self.input_manifest('link-inputs', [obj, *c_objects, cc, shim_source, init, *extra_inputs])
        shim_t = self.transcript('shim.transcript', cc, shim_args)
        link_t = self.transcript('link.transcript', cc, link_args)
        shim_rss, link_rss = self.rss('shim.rss.env', '0'), self.rss('link.rss.env', '0')
        link_result = self.receipt('link.env', {'shim_raw_status': 0, 'link_raw_status': 0,
             'guard_validation_status': 0, 'boundaries': 'PASS', 'artifact_sha256': m.sha(artifact)})
        paths = {'object': obj, 'artifact': artifact, 'build_log': log, 'build_transcript': build_t,
             'build_rss': build_rss, 'qualification': qualification, 'link_result': link_result,
             'link_inputs': linked, 'shim_transcript': shim_t, 'shim_rss': shim_rss,
             'link_transcript': link_t, 'link_rss': link_rss, 'c_runtime_manifest': c_manifest,
             'shim_source': shim_source, 'shim_object': shim_object, 'module_init': init, 'toolchain': toolchain}
        inputs = self.input_manifest('product-inputs', list(paths.values()))
        d = {'schema': 'simple-retained-manual-product-v1', 'producer_path': str(producer),
             'producer_sha256': m.sha(producer), 'source_root': str(self.root), 'runtime_path': '/retained/runtime',
             'entry': 'entry.spl', 'build_raw_status': raw, 'cc_path': str(cc), 'cc_sha256': m.sha(cc),
             'inputs_path': str(inputs), 'inputs_sha256': m.sha(inputs)}
        for k, p in paths.items():
            d[k+'_path'], d[k+'_sha256'] = str(p), m.sha(p)
        return self.receipt('product.env', d), d

    def refresh_product(self, receipt, d):
        for key in list(d):
            if key.endswith('_path') and key[:-5]+'_sha256' in d:
                d[key[:-5]+'_sha256'] = m.sha(d[key])
        inputs = Path(d['inputs_path'])
        paths = [row.split('|')[1] for row in inputs.read_text().splitlines()]
        inputs.write_text(''.join(m.sha(p)+'|'+p+'\n' for p in paths))
        d['inputs_sha256'] = m.sha(inputs)
        receipt.write_text(''.join(k+'='+str(v)+'\n' for k, v in d.items()))

    def log(self, raw='1', extra=''):
        obj = self.root/'aggregate.o'
        lines = ('[build] phase=mir state=running unit_kind=modules done=2 total=2 remaining=0 succeeded=2 cached=0 failed=0 current=lower_to_mir\n'
                 '[build] phase=native_compile state=running unit_kind=modules done=2 total=2 remaining=0 succeeded=1 cached=1 failed=0 current=complete\n')
        lines += '[native-build] Artifact published: '+str(obj)+'\n'
        if raw == '1':
            lines += 'error: native-build worker exited 0 but produced no output binary: '+str(obj)+'\n'
        return self.text('native.log', lines+extra), obj

    def test_named_coordinator_false_negative_keeps_raw1(self):
        log, obj = self.log()
        counts = m.native_log(log, '1', obj)
        self.assertEqual((counts['succeeded'], counts['cached']), (1, 1))

    def test_other_raw1_or_missing_publication_diagnostic_rejected(self):
        log, obj = self.log('0')
        with self.assertRaises(ValueError):
            m.native_log(log, '1', obj)
        log, obj = self.log('1', 'error: actual native failure\n')
        with self.assertRaises(ValueError):
            m.native_log(log, '1', obj)

    def test_failed_modules_ice_drop_and_wrong_worker_path_rejected(self):
        for bad in ('[build] phase=mir failed=1\n', 'LLVM ERROR: broken IR\n', 'DROPPED to wildcard\n'):
            log, obj = self.log('0', bad)
            with self.assertRaises(ValueError):
                m.native_log(log, '0', obj)
        log, obj = self.log()
        with self.assertRaises(ValueError):
            m.native_log(log, '1', self.root/'different.o')

    def test_profile_warning_is_not_native_failure(self):
        log, obj = self.log('0', 'aot:mir_errors:item non-exhaustive enum profile warning\n')
        self.assertEqual(m.native_log(log, '0', obj)['failed'], 0)

    def test_missing_mir_or_native_completion_rejected(self):
        log, obj = self.log('0')
        log.write_text(log.read_text().splitlines()[1]+'\n')
        with self.assertRaises(ValueError):
            m.native_log(log, '0', obj)

    def test_completed_log_without_actual_publication_cannot_qualify_stale_object(self):
        log, obj = self.log()
        log.write_text('\n'.join(line for line in log.read_text().splitlines() if 'Artifact published:' not in line)+'\n')
        with self.assertRaisesRegex(ValueError, 'aggregate publication'):
            m.native_log(log, '1', obj)

    def test_qualified_phase_reuses_retained_object_without_compiler_run(self):
        obj = self.header('aggregate.o', 1); producer = self.header('producer', 2)
        log, _ = self.log()
        (self.root/'object.log').write_bytes(log.read_bytes())
        self.rss('object.log.rss.env', '1')
        argv = [str(producer), 'native-build', '--entry', 'entry.spl', '--emit-object', '-o', str(obj)]
        argv_file = self.root/'object.argv'; argv_file.write_bytes(b'\0'.join(x.encode() for x in argv)+b'\0')
        self.receipt('object-build.env', {'raw_status': 1, 'producer_sha256': m.sha(producer),
             'object_sha256': m.sha(obj), 'argv_sha256': m.sha(argv_file)})
        with patch.object(m, 'run_command') as run:
            actual, _, raw = m.retained_object(self.root, argv, str(producer), '/source', '/runtime', ROOT, False)
            self.assertEqual(actual, obj); self.assertEqual(raw['raw_status'], '1'); run.assert_not_called()
        with patch.object(m, 'run_command') as run:
            with self.assertRaisesRegex(ValueError, 'retained argv changed'):
                m.retained_object(self.root, [*argv, '--source', 'different'], str(producer), '/source', '/runtime', ROOT, False)
            run.assert_not_called()

    def test_qualified_phase_cannot_compile_missing_preparation(self):
        with patch.object(m, 'run_command') as run:
            with self.assertRaisesRegex(ValueError, 'object preparation first'):
                m.retained_object(self.root, ['/P3b', 'native-build'], '/P3b', '/source', '/runtime', ROOT, False)
            run.assert_not_called()

    def test_object_preparation_cannot_link_or_publish_readiness(self):
        producer = self.header('producer', 2)
        config = {'sdk_path': '/retained/sdk'}
        for name in ('cc', 'nm', 'entry_template', 'sdk_settings'):
            path = self.text(name+'-pin', 'synthetic '+name+' pin')
            config[name+'_path'], config[name+'_sha256'] = str(path), m.sha(path)
        toolchain = self.receipt('toolchain.env', config)
        c_manifest = self.text('c-runtime.manifest', 'not opened during object-only preparation')
        authority = {'toolchain_path': str(toolchain), 'toolchain_sha256': m.sha(toolchain),
                     'c_runtime_manifest_path': str(c_manifest), 'c_runtime_manifest_sha256': m.sha(c_manifest)}
        sources = ['src/compositions/kernel_llvm_cranelift', 'src/compiler', 'src/app', 'src/lib', 'src/os']
        original = ['native-build', '--runtime-bundle', 'host-gpu',
                    *[v for source in sources for v in ('--source', source)], '--entry', m.ROLES['compiler_cli_build'],
                    '--cache-dir', '/normal/producer-owned/cache', '--output', str(self.root/'cli')]
        args = SimpleNamespace(chain=str(self.root/'chain.env'), selected=str(producer), producer=str(producer),
             source=str(self.root), original_runtime='/original/runtime', runtime='/retained/capsule',
             role='compiler_cli_build', argv=original, work=str(self.root/'role-work'),
             qualification=str(self.root/'independent.env'), output=str(self.root/'cli'), prepare_only=True)
        # Even an existing review file cannot turn the objects-only phase into
        # link/readiness. The file is deliberately not a valid qualification.
        Path(args.qualification).write_text('synthetic test marker, never read in preparation phase\n')
        with patch.object(m, 'chain', return_value=authority), patch.object(m.legacy, 'verify_capsule_copy'), \
             patch.object(m, 'retained_object', return_value=(self.root/'role-work/aggregate.o', self.root/'build.env', {'raw_status': '1'})), \
             patch.object(m, 'run_command') as run, patch.object(m, 'product') as publish:
            self.assertEqual(m.build_tool(args), 86)
            run.assert_not_called(); publish.assert_not_called()
        self.assertFalse(Path(args.output).exists())
        self.assertFalse((Path(args.work)/'product.env').exists())

    def test_regular_arm64_object_and_executable_headers(self):
        obj = self.header('obj', 1); exe = self.header('exe', 2)
        m.macho(obj, 1); m.macho(exe, 2)
        with self.assertRaises(ValueError):
            m.macho(obj, 2)
        exe.chmod(0o600)
        with self.assertRaises(ValueError):
            m.macho(exe, 2)
        link = self.root/'symlink'; link.symlink_to(obj)
        with self.assertRaises(ValueError):
            m.macho(link, 1)

    def test_stale_manifest_and_duplicate_inputs_fail(self):
        p = self.text('input', 'real synthetic evidence')
        manifest = self.text('inputs', m.sha(p)+'|'+str(p)+'\n')
        self.assertEqual(m.manifest(manifest)[str(p)], m.sha(p))
        p.write_text('changed')
        with self.assertRaises(ValueError):
            m.manifest(manifest)
        manifest.write_text((m.sha(p)+'|'+str(p)+'\n')*2)
        with self.assertRaises(ValueError):
            m.manifest(manifest)

    def test_role_argv_preserves_sources_runtime_target_and_normal_cache(self):
        for role, entry in m.ROLES.items():
            args = ['native-build', '--target', 'aarch64-apple-darwin', '--runtime-bundle', 'host-gpu',
                    '--runtime-path', '/retained/capsule', '--source', 'src/compiler', '--source', 'src/app',
                    '--entry-closure', '--entry', entry, '--threads', '4', '--cache-dir', '/normal/cache',
                    '--output', '/normal/output']
            actual = m.tool_argv('/actual/P3b', args, '/new/aggregate.o')
            expected = list(args); expected[-1] = '/new/aggregate.o'
            self.assertEqual(actual, ['/actual/P3b', *expected, '--emit-object', '--mode', 'dynload'])
            self.assertEqual(args[-1], '/normal/output')

    def test_multiple_output_or_existing_mode_rejected(self):
        for argv in (['native-build', '-o', 'a', '--output', 'b'], ['native-build', '-o', 'a', '--mode', 'dynload']):
            with self.assertRaises(ValueError):
                m.tool_argv('/P3b', argv, '/object')

    def test_exact_argv_launcher_and_actual_producer_join(self):
        compiler = self.header('compiler', 2)
        launcher = self.root/'argv-exec.py'; launcher.write_bytes(m.ARGV_LAUNCHER)
        argv = self.root/'version.argv'; argv.write_bytes(str(compiler).encode()+b'\0--version\0')
        def transcript(exe, args):
            rows = [('cwd', str(self.root)), ('executable', exe), *[('argv', a) for a in args]]
            return 'schema=simple-bootstrap-command-transcript-v2\n'+''.join(k+':'+str(len(v.encode()))+':'+v+'\n' for k, v in rows)
        log = self.text('version.transcript', transcript('/usr/bin/python3', [str(launcher), str(argv)]))
        d = {}
        for key, p in [('version_transcript', log), ('version_launcher', launcher), ('version_argv', argv)]:
            d[key+'_path'], d[key+'_sha256'] = str(p), m.sha(p)
        args, _ = m.invocation(d, 'version', str(compiler), str(self.root), ['--version'])
        self.assertEqual(args, ['--version'])
        with self.assertRaises(ValueError):
            m.invocation(d, 'version', '/wrong/producer', str(self.root), ['--version'])
        launcher.write_text('print("fake")')
        d['version_launcher_sha256'] = m.sha(launcher)
        with self.assertRaises(ValueError):
            m.invocation(d, 'version', str(compiler), str(self.root), ['--version'])

    def test_source_and_runtime_swap_fail_before_any_execution(self):
        receipt = self.text('chain.env', 'schema=simple-stage4-retained-manual-self-v1\nruntime_path=/retained/runtime\n')
        with self.assertRaises((ValueError, KeyError)):
            m.chain(receipt, '/wrong/P3b', '/wrong/source', '/wrong/runtime')
        with patch.object(m, 'source_map', side_effect=ValueError('wrong source')):
            with self.assertRaises((ValueError, KeyError)):
                m.chain(receipt, '/P3b', '/wrong/source', '/runtime')

    def test_complete_explicit_product_contract_preserves_raw1(self):
        receipt, d = self.product_fixture()
        verified = m.product(receipt, producer=d['producer_path'], source=d['source_root'], runtime=d['runtime_path'])
        self.assertEqual(verified['build_raw_status'], '1')
        self.assertEqual(verified['artifact_sha256'], m.sha(d['artifact_path']))

    def test_actual_response_file_shape_is_accepted(self):
        receipt, d = self.product_fixture(response=True)
        self.assertEqual(m.product(receipt)['build_raw_status'], '1')

    def test_omitted_initializer_with_regenerated_pinned_shim_is_rejected(self):
        receipt, d = self.product_fixture(response=True)
        Path(d['module_init_path']).write_text('')
        config = m.env(d['toolchain_path'])
        Path(d['shim_source_path']).write_text(m.canonical_shim(config['entry_template_path'], []))
        linked = Path(d['link_inputs_path'])
        paths = [row.split('|')[1] for row in linked.read_text().splitlines()]
        linked.write_text(''.join(m.sha(p)+'|'+p+'\n' for p in paths))
        self.refresh_product(receipt, d)
        with self.assertRaisesRegex(ValueError, 'initializer inventory does not match actual aggregate'):
            m.product(receipt)

    def test_changed_response_or_extra_unbound_provider_rejected(self):
        receipt, d = self.product_fixture(response=True)
        response = self.root/'link.args'
        args = [json.loads(line) for line in response.read_text().splitlines()]
        args.insert(1, str(self.root/'unbound-extra.o'))
        response.write_text(''.join(json.dumps(x)+'\n' for x in args))
        with self.assertRaises(ValueError):
            m.product(receipt)
        linked = Path(d['link_inputs_path'])
        paths = [row.split('|')[1] for row in linked.read_text().splitlines()]
        linked.write_text(''.join(m.sha(p)+'|'+p+'\n' for p in paths))
        self.refresh_product(receipt, d)
        with self.assertRaisesRegex(ValueError, 'changed/unbound link provider'):
            m.product(receipt)

    def test_correct_coordinator_cannot_dispatch_wrong_worker_binary(self):
        receipt, d = self.product_fixture()
        transcript = Path(d['build_transcript_path'])
        text = transcript.read_text()
        old = 'SIMPLE_BINARY='+d['producer_path']; new = 'SIMPLE_BINARY=/wrong/P2'
        text = text.replace('explicit-env:'+str(len(old.encode()))+':'+old,
                            'explicit-env:'+str(len(new.encode()))+':'+new)
        transcript.write_text(text)
        self.refresh_product(receipt, d)
        with self.assertRaisesRegex(ValueError, 'wrong worker/runtime selector: SIMPLE_BINARY'):
            m.product(receipt)

    def test_real_runtime_snapshot_facade_overrides_inherited_wrong_facade(self):
        runtime = self.root/'retained'; runtime.mkdir()
        (runtime/'retained-input').write_text('tiny retained input; no compilation')
        output = self.root/'runtime.snapshot'
        facade = ROOT/'scripts/check/lib/bootstrap-stage3-provenance.shs'
        with patch.dict(os.environ, {'BOOTSTRAP_STAGE3_FACADE_PATH': '/wrong/inherited/facade'}):
            m.runtime_snapshot(facade, output, runtime)
            self.assertEqual(os.environ['BOOTSTRAP_STAGE3_FACADE_PATH'], '/wrong/inherited/facade')
        self.assertIn(m.sha(runtime/'retained-input'), output.read_text())

    def test_controller_bundle_rejects_changed_companion_after_initial_pin(self):
        helper = self.text('controller-helper', 'initial controller code')
        bundle = self.input_manifest('controller-bundle', [helper])
        initial = m.sha(bundle)
        m.manifest(bundle)
        helper.write_text('concurrent changed controller code')
        self.assertEqual(m.sha(bundle), initial)
        with self.assertRaises(ValueError):
            m.manifest(bundle)

    @unittest.skipUnless(hasattr(os, 'chflags'), 'macOS physical freeze contract')
    def test_full_source_map_reopens_tracked_bytes_and_nested_gitlinks(self):
        original, payload = self.root/'original', self.root/'payload'
        original.mkdir()
        def git(root, *args):
            return subprocess.check_output(['git', '-C', str(root), *args], stderr=subprocess.PIPE)
        git(original, 'init', '-q')
        tracked = original/'tracked.txt'; tracked.write_text('original tracked bytes\n')
        nested = original/'nested'; nested.mkdir()
        git(nested, 'init', '-q'); (nested/'nested.txt').write_text('nested tracked bytes\n')
        git(nested, 'add', 'nested.txt')
        git(nested, '-c', 'user.name=Contract', '-c', 'user.email=contract@example.invalid', 'commit', '-qm', 'nested fixture')
        git(original, 'add', 'tracked.txt', 'nested')
        git(original, '-c', 'user.name=Contract', '-c', 'user.email=contract@example.invalid', 'commit', '-qm', 'source fixture')
        subprocess.check_output(['git', 'clone', '-q', str(original), str(payload)], stderr=subprocess.PIPE)
        subprocess.check_output(['git', 'clone', '-q', str(nested), str(payload/'nested')], stderr=subprocess.PIPE)
        head = git(original, 'rev-parse', 'HEAD').decode().strip()
        tree = git(original, 'rev-parse', 'HEAD^{tree}').decode().strip()
        source_stat, root_stat = tracked.lstat(), original.lstat()
        plan = self.root/'plan.json'; status = self.root/'status.json'
        records = []
        for path, saved, kind in [(tracked, source_stat, 'file'), (original, root_stat, 'dir')]:
            records.append({'path': str(path), 'dev': saved.st_dev, 'ino': saved.st_ino, 'kind': kind,
                            'mode': stat.S_IMODE(saved.st_mode), 'flags': saved.st_flags})
        plan.write_text(json.dumps({'source_root': str(original), 'source_head': head, 'records': records}))
        status.write_text(json.dumps({'source_root': str(original), 'source_head': head, 'plan': str(plan),
                         'status': 'protected', 'source_clean': True, 'protected_files': 1, 'protected_dirs': 1}))
        present = self.input_manifest('original-present', [tracked])
        data = {'schema': 'simple-retained-source-map-v1', 'original_root': str(original),
                'payload_root': str(payload), 'source_head': head, 'source_tree': tree}
        for key, path in {'freeze_plan': plan, 'freeze_status': status, 'original_present': present}.items():
            data[key+'_path'], data[key+'_sha256'] = str(path), m.sha(path)
        source_map = self.receipt('source-map.env', data)
        tracked.chmod(stat.S_IMODE(source_stat.st_mode) & ~0o222)
        original.chmod(stat.S_IMODE(root_stat.st_mode) & ~0o222)
        try:
            os.chflags(tracked, source_stat.st_flags | stat.UF_IMMUTABLE)
            self.assertEqual(m.source_map(source_map, str(payload))['source_tree'], tree)
            # A matching HEAD and clean status with an assume-unchanged bit
            # cannot hide changed tracked bytes from the actual Git blob join.
            git(payload, 'update-index', '--assume-unchanged', 'tracked.txt')
            (payload/'tracked.txt').write_text('changed but status-hidden bytes\n')
            self.assertEqual(git(payload, 'status', '--porcelain'), b'')
            with self.assertRaisesRegex(ValueError, 'tracked bytes changed'):
                m.source_map(source_map, str(payload))
            (payload/'tracked.txt').write_bytes(tracked.read_bytes())
            (payload/'nested'/'nested.txt').write_text('changed nested module\n')
            with self.assertRaises(ValueError):
                m.source_map(source_map, str(payload))
        finally:
            os.chflags(tracked, source_stat.st_flags)
            tracked.chmod(stat.S_IMODE(source_stat.st_mode))
            original.chmod(stat.S_IMODE(root_stat.st_mode))

    def test_product_wrong_producer_source_runtime_or_missing_link_fails(self):
        receipt, d = self.product_fixture()
        for kwargs in ({'producer': '/wrong/producer'}, {'source': '/wrong/source'}, {'runtime': '/wrong/runtime'}):
            with self.assertRaises(ValueError):
                m.product(receipt, **kwargs)
        Path(d['link_result_path']).unlink()
        with self.assertRaises(ValueError):
            m.product(receipt)

    def test_product_stale_object_or_qualification_fails(self):
        receipt, d = self.product_fixture()
        Path(d['qualification_path']).write_text('schema=fabricated\n')
        with self.assertRaises(ValueError):
            m.product(receipt)

    def test_product_rejects_missing_published_object(self):
        receipt, d = self.product_fixture()
        Path(d['object_path']).unlink()
        with self.assertRaises(ValueError):
            m.product(receipt)

    def test_explicit_chain_connects_fixed_p2_p3a_and_selected_p3b(self):
        # Product/source/sanity validators have independent positive tests;
        # this fixture isolates the chain's actual cross-validator joins.
        original = self.root/'frozen'; original.mkdir()
        template = original/'src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl'
        template.parent.mkdir(parents=True); template.write_text('bound frozen template')
        p2 = self.header('fixed-p2', 2); pa = self.header('p3a', 2); pb = self.header('p3b', 2)
        p2_log = self.text('p2.log', 'retained historical PASS')
        p2_t = self.text('p2.transcript', 'retained historical transcript')
        p2_rss = self.rss('p2.rss', '0')
        runtime_snapshot = self.text('runtime.snapshot', 'actual bound synthetic runtime bytes')
        runtime = str(self.root/'runtime')
        p2_result = self.receipt('fixed-p2.env', {'schema': 'pure-spl-aliasfix-p2-native-build-v1',
            'native_build_raw_status': 0, 'artifact_status': 'present', 'artifact_path': p2, 'artifact_sha256': m.sha(p2),
            'runtime_snapshot_sha256': m.sha(runtime_snapshot), 'native_build_log': p2_log,
            'native_build_log_sha256': m.sha(p2_log), 'native_build_transcript': p2_t,
            'native_build_transcript_sha256': m.sha(p2_t), 'rss_receipt': p2_rss, 'rss_receipt_sha256': m.sha(p2_rss)})
        toolchain = self.receipt('chain-toolchain.env', {'entry_template_path': template, 'entry_template_sha256': m.sha(template)})
        paths = {'source_map': self.text('mapped-source', 'source contract is separately validated'),
            'producer_product': self.text('producer-product', 'separately validated producer product'),
            'producer_sanity': self.text('producer-sanity', 'separately validated producer sanity'),
            'self_product': self.text('self-product', 'separately validated self product'),
            'self_sanity': self.text('self-sanity', 'separately validated self sanity'),
            'runtime_snapshot': runtime_snapshot, 'fixed_p2': p2, 'fixed_p2_result': p2_result,
            'toolchain': toolchain, 'c_runtime_manifest': self.text('chain-c-manifest', 'independent retained C proof')}
        inputs = self.input_manifest('chain-inputs', list(paths.values()))
        d = {'schema': 'simple-stage4-retained-manual-self-v1', 'runtime_path': runtime,
             'inputs_path': str(inputs), 'inputs_sha256': m.sha(inputs)}
        for name, path in paths.items():
            d[name+'_path'], d[name+'_sha256'] = str(path), m.sha(path)
        receipt = self.receipt('chain.env', d)
        sm = {'original_root': str(original), 'source_head': 'a'*40, 'source_tree': 'b'*40}
        base = {'entry': 'src/app/cli/bootstrap_main.spl', 'source_head': sm['source_head'], 'source_tree': sm['source_tree'],
            'runtime_snapshot_sha256': d['runtime_snapshot_sha256'], 'c_runtime_manifest_path': d['c_runtime_manifest_path'],
            'c_runtime_manifest_sha256': d['c_runtime_manifest_sha256'], 'toolchain_path': str(toolchain),
            'toolchain_sha256': m.sha(toolchain), 'source_root': str(original)}
        a = dict(base, artifact_path=str(pa), producer_path=str(p2))
        b = dict(base, artifact_path=str(pb), producer_path=str(pa))
        version = self.text('same-version', 'simple-bootstrap test-contract\n')
        sources = ['src/compositions/kernel_llvm_cranelift', 'src/compositions/cuda_static',
                   'src/compiler', 'src/app', 'src/lib', 'src/plugins']
        argv = ['native-build', *[v for source in sources for v in ('--source', source)]]
        def snapshot(facade, output, selected_runtime):
            Path(output).write_bytes(runtime_snapshot.read_bytes())
        with patch.object(m, 'source_map', return_value=sm), patch.object(m, 'runtime_snapshot', side_effect=snapshot), \
             patch.object(m, 'product', side_effect=[a, b]) as products, \
             patch.object(m, 'sanity', return_value={'version_stdout_path': str(version)}), \
             patch.object(m, 'invocation', return_value=(argv, [])):
            self.assertEqual(m.chain(receipt, str(pb), '/mapped-payload', runtime)['runtime_path'], runtime)
            self.assertEqual(products.call_args_list[0].kwargs['producer'], str(p2))
            self.assertEqual(products.call_args_list[1].kwargs['producer'], str(pa))
        with patch.object(m, 'source_map', return_value=sm):
            with self.assertRaisesRegex(ValueError, 'field mismatch: runtime_path'):
                m.chain(receipt, str(pb), '/mapped-payload', '/wrong-runtime')

    def test_legacy_validator_bytes_unchanged(self):
        rel = 'scripts/check/lib/stage4-retained-self-evidence.py'
        original = subprocess.check_output(['git', '-C', str(ROOT), 'show', '37cc365401249d23364c9c56868295de40557104:'+rel])
        self.assertEqual((ROOT/rel).read_bytes(), original)

    def test_controller_rejects_implicit_or_mixed_manual_lane(self):
        script = ROOT/'scripts/bootstrap/bootstrap-phase-verification.shs'
        for args in (['--phase=stage4', '--stage3-retained-manual-receipt=/missing'],
                     ['--phase=stage4', '--stage3-retained-manual-receipt=/missing',
                      '--manual-tool-qualifications=/missing', '--stage3-original-runtime=/missing',
                      '--stage3-self-rebuild-result=/legacy']):
            result = subprocess.run(['sh', str(script), *args], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('manual retained lane', result.stderr)


if __name__ == '__main__':
    unittest.main()

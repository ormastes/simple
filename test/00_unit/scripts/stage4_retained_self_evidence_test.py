#!/usr/bin/env python3
"""Synthetic receipt-contract tests only. No compiler/application is executed."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('evidence', ROOT / 'scripts/check/lib/stage4-retained-self-evidence.py')
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)


class ReceiptContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = str(self.base / 'source')
        Path(self.root).mkdir()
        self.original = str(self.base / 'runtime-generation')
        Path(self.original).mkdir()
        self.a = self.put('p3a', b'synthetic producer')
        self.b = self.put('p3b', b'synthetic self product')
        self.cli = self.put('cli', b'synthetic cli')
        self.runner = self.put('runner', b'synthetic runner')
        self.mcp = self.put('mcp', b'synthetic mcp')
        self.lsp = self.put('lsp', b'synthetic lsp')
        marker = self.put('marker', b'fixed synthetic input')
        self.inputs = self.put('inputs', (marker + '|' + e.sha(marker) + '\n').encode())
        p2 = self.put('p2', b'synthetic prior compiler')
        plog = self.put('producer/build.log', b'completed')
        ptr = self.tr('producer/build.tr', p2, ['native-build'])
        prss = self.rss('producer/build.rss', 10)
        pbuild = self.receipt('producer/build.env', raw_status=0, p3_output=self.a, p3_log=plog, p3_transcript=ptr, p3_rss_receipt=prss)
        self.p = self.receipt('producer/result.env', p2_path=p2, p2_sha256=e.sha(p2), dropped_to_wildcard=0,
            p3_build_receipt=pbuild, p3_build_receipt_sha256=e.sha(pbuild), p3_log=plog, p3_log_sha256=e.sha(plog),
            p3_transcript=ptr, p3_transcript_sha256=e.sha(ptr), p3_rss=prss, p3_rss_sha256=e.sha(prss),
            source_snapshot_before_sha256='source-digest', schema='aliasfix-p3-diagnostic-v1', source_root=self.root,
            source_head='HEAD', runtime_snapshot_sha256='runtime-digest', p3_path=self.a, p3_sha256=e.sha(self.a),
            immutable_inputs_manifest=self.inputs, immutable_inputs_manifest_sha256=e.sha(self.inputs))
        self.pg = self.gates('producer/gates', self.a, self.p)
        log = self.put('self/build.log', b'completed')
        tr = self.tr('self/build.transcript', self.a, ['native-build', '--mode', 'dynload', '--entry', 'src/app/cli/bootstrap_main.spl', '-o', self.b, '--runtime-path', self.original] + [a for source in ['src/compositions/kernel_llvm_cranelift', 'src/compositions/cuda_static', 'src/compiler', 'src/app', 'src/lib', 'src/plugins'] for a in ['--source', source]])
        rss = self.rss('self/build.rss', 10)
        br = self.receipt('self/build.env', raw_status=0, p3b_output=self.b, p3b_log=log, p3b_transcript=tr, p3b_rss_receipt=rss)
        self.r = self.receipt('self/result.env', schema='aliasfix-p3-self-rebuild-v1', diagnostic_only=1,
            admission_status='NOT_ATTEMPTED', publication_status='NOT_ATTEMPTED', native_build_raw_status=0,
            source_root=self.root, source_head='HEAD', source_snapshot_sha256='source-digest', p3b_path=self.b,
            p3b_sha256=e.sha(self.b), runtime_generation=Path(self.original).name, runtime_snapshot_sha256='runtime-digest',
            inputs_manifest=self.inputs, inputs_manifest_sha256=e.sha(self.inputs), producer_path=self.a,
            producer_sha256=e.sha(self.a), producer_result=self.p, producer_result_sha256=e.sha(self.p),
            producer_gates=self.pg, producer_gates_sha256=e.sha(self.pg), build_receipt=br, build_receipt_sha256=e.sha(br),
            log_path=log, log_sha256=e.sha(log), transcript_path=tr, transcript_sha256=e.sha(tr),
            rss_receipt_path=rss, rss_receipt_sha256=e.sha(rss), dropped_to_wildcard=0)
        self.sg = self.gates('selected/gates', self.b, self.r)
        # Only Git identity lookup is stubbed; receipt bytes/hashes/graphs are real.
        self.git = patch.object(e.subprocess, 'check_output', side_effect=lambda args, **kw:
            ('TREE' if args[-1] == 'HEAD^{tree}' else 'HEAD') if 'rev-parse' in args else b'')
        self.git.start(); self.addCleanup(self.git.stop)

    def put(self, rel, data):
        p = self.base / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(data); p.chmod(0o700)
        return str(p)

    def receipt(self, rel, **items):
        return self.put(rel, ''.join(str(k) + '=' + str(v) + '\n' for k, v in items.items()).encode())

    def tr(self, rel, binary, args, settings=()):
        rows = ['schema=simple-bootstrap-command-transcript-v2', 'runtime-env-contract:bootstrap-session-v1']
        for key, val in [('cwd', self.root), ('executable', binary)] + [('explicit-env', a) for a in settings] + [('argv', a) for a in args]:
            rows.append(key + ':' + str(len(val.encode())) + ':' + val)
        return self.put(rel, ('\n'.join(rows) + '\n').encode())

    def rss(self, rel, jobs):
        return self.receipt(rel, status='complete', exit_status=0, quiescent=1, rss_cap_mode='enforce', rss_cap_enforced=1,
            observer_errors=0, observer_restarts=0, measurement_budget_complete=1, sample_budget_exceeded=0,
            compiler_jobs=jobs, max_rss_kib=13631488)

    def gates(self, rel, binary, result):
        hello = self.put(rel + '/hello', b'synthetic hello executable')
        fields = dict(schema='aliasfix-p3-version-hello-gates-v1', p3_path=binary, p3_sha256=e.sha(binary),
            p3_result=result, p3_result_sha256=e.sha(result), source_head='HEAD', runtime_snapshot_sha256='runtime-digest',
            p3_version_status=0, p3_native_hello_build_status=0, p3_native_hello_run_status=0, p3_version_match_p2=1,
            inputs_manifest=self.inputs, inputs_manifest_sha256=e.sha(self.inputs), hello_binary=hello, hello_binary_sha256=e.sha(hello))
        for name, key, output, jobs, args in [('p3-version', 'version_receipt_sha256', binary, 0, ['--version']),
            ('p3-hello-build', 'hello_build_receipt_sha256', hello, 10, ['native-build', '--runtime-path', self.original, '--mode', 'one-binary', '--entry', self.root + '/test/04_smoke/bootstrap_hello_world.spl', '-o', hello]),
            ('p3-hello-run', 'hello_run_receipt_sha256', hello, 0, [])]:
            log = self.put(rel + '/' + name + '.log', b'hello\n' if name == 'p3-hello-run' else b'simple-bootstrap 1.0.0\n')
            settings = ['DYLD_LIBRARY_PATH=' + self.original]
            if name == 'p3-hello-build': settings += ['SIMPLE_RUNTIME_PATH=' + self.original, 'SIMPLE_BINARY=' + binary, 'SIMPLE_BOOTSTRAP=1']
            tr = self.tr(rel + '/' + name + '.tr', hello if name == 'p3-hello-run' else binary, args, settings)
            rss = self.rss(rel + '/' + name + '.rss', jobs)
            receipt = self.receipt(rel + '/' + name + '.env', task=name, raw_status=0, output_path=output,
                log_path=log, log_sha256=e.sha(log), transcript_path=tr, transcript_sha256=e.sha(tr),
                rss_receipt_path=rss, rss_receipt_sha256=e.sha(rss))
            fields[key] = e.sha(receipt)
            if name == 'p3-version': fields['version_log'] = log
            if name == 'p3-hello-run': fields['hello_run_log'] = log
        return self.receipt(rel + '/gates.env', **fields)

    def check(self):
        return e.verify_self(self.r, self.b, self.root, self.original, self.sg)

    def test_valid_synthetic_chain(self):
        self.assertEqual(self.check()['p3b_path'], self.b)

    def test_reject_each_changed_authority(self):
        for path in (self.a, self.b, self.inputs, self.p, self.pg, self.sg):
            with self.subTest(path=path):
                original = Path(path).read_bytes(); Path(path).write_bytes(original + b'changed')
                with self.assertRaises((ValueError, KeyError)): self.check()
                Path(path).write_bytes(original)

    def test_reject_duplicate_pending_nonzero_and_swap(self):
        original = Path(self.r).read_text()
        for data in (original + 'source_head=HEAD\n', original.replace('native_build_raw_status=0', 'native_build_raw_status=1'),
                     original.replace('source_head=HEAD', 'source_head=PENDING'), original.replace('p3b_path=' + self.b, 'p3b_path=' + self.a)):
            with self.subTest(data=data[-60:]):
                Path(self.r).write_text(data)
                with self.assertRaises(ValueError): self.check()
        Path(self.r).write_text(original)

    def test_nonquiescent_rss_rejected_even_when_rehashed(self):
        r = e.env(self.r); path = r['rss_receipt_path']
        Path(path).write_text(Path(path).read_text().replace('quiescent=1', 'quiescent=0'))
        r['rss_receipt_sha256'] = e.sha(path)
        Path(self.r).write_text(''.join(k + '=' + v + '\n' for k, v in r.items()))
        # Rebind selected gate to changed result so failure tests RSS semantics.
        g = e.env(self.sg); g['p3_result_sha256'] = e.sha(self.r)
        Path(self.sg).write_text(''.join(k + '=' + v + '\n' for k, v in g.items()))
        with self.assertRaisesRegex(ValueError, 'quiescent'): self.check()

    def test_wrong_transcript_owner_rejected(self):
        tr = self.tr('wrong.tr', self.a, ['--version'])
        with self.assertRaisesRegex(ValueError, 'executable'):
            e.transcript(tr, self.b, self.root, ['--version'])

    def candidate(self):
        capsule = self.base / 'capsule'; capsule.mkdir()
        for rel, data in [('libsimple_native_all.a', b'native archive'), ('hosted-runtime.env', b'sha256=hosted-digest\nrelative_path=deps/libspl_hosted_runtime.rlib\n'), ('deps/libspl_hosted_runtime.rlib', b'hosted bytes'), ('simple.inputs.sha256', b'stamp')]:
            self.put('runtime-generation/' + rel, data); self.put('capsule/' + rel, data)
        cap = self.receipt('capsule/phase2-runtime-capsule.env', schema='simple-phase2-runtime-capsule-v2', status='frozen',
            compiler_sha256=e.sha(self.b), source_authority_path=self.original)
        cmd = self.receipt('owners/command.env', schema='simple-bootstrap-command-owners-v3', status='frozen', phase='stage4',
            compiler_snapshot_sha256=e.sha(self.b), compiler_cli_path=self.cli, compiler_cli_sha256=e.sha(self.cli),
            test_runner_path=self.runner, test_runner_sha256=e.sha(self.runner), mcp_server_path=self.mcp, mcp_server_sha256=e.sha(self.mcp))
        tools = self.receipt('owners/tools.env', schema='simple-bootstrap-stage4-tooling-owners-v1', status='frozen', phase='stage4',
            compiler_snapshot_path=self.b, compiler_snapshot_sha256=e.sha(self.b), command_owner_receipt_path=cmd,
            command_owner_receipt_sha256=e.sha(cmd), hosted_runtime_path=str(capsule), hosted_runtime_sha256='hosted-digest',
            mcp_server_path=self.mcp, mcp_server_sha256=e.sha(self.mcp), lsp_server_path=self.lsp, lsp_server_sha256=e.sha(self.lsp))
        controller = str(ROOT / 'scripts/bootstrap/bootstrap-phase-verification.shs')
        helper = str(ROOT / 'scripts/check/lib/stage4-candidate-provenance.shs')
        owner = self.put('source/scripts/check/check-bootstrap-essential-tools-smoke.shs', b'synthetic smoke owner, not executed')
        fields = dict(schema='simple-stage4-retained-self-provenance-v1', status='pass', artifact_kind='pure-simple-full-cli',
            output_path=self.cli, output_sha256=e.sha(self.cli), source_root=self.root, source_head='HEAD', source_tree='TREE',
            source_snapshot_sha256='source-digest', parent_compiler_path=self.b, parent_compiler_sha256=e.sha(self.b),
            original_runtime_path=self.original, runtime_path=str(capsule), runtime_snapshot_sha256='runtime-digest',
            completed_gate='stage4-essential-tools-smoke', whole_suite_status='NOT_CLAIMED')
        smoke_log = self.put('smoke.log', b'essential_tools_pure_simple_identity=true\nessential_test_runner_smoke=true\nessential_lint_smoke=true\nessential_duplicate_checker_smoke=true\nbootstrap_essential_tools_smoke=true\n')
        fields['essential_tools_log_path'] = smoke_log; fields['essential_tools_log_sha256'] = e.sha(smoke_log)
        receipts = {}
        for key, task, args in [('build_receipt', 'compiler_cli_build', [self.b, 'native-build', '--entry', 'src/app/cli/_CliMain/main_and_help.spl', '--output', self.cli]),
                               ('smoke_receipt', 'stage4_essential_tools', ['env', 'SIMPLE_BINARY=' + self.cli, 'sh', owner])]:
            log = smoke_log if key == 'smoke_receipt' else self.put('cli.log', b'compiled')
            argv = self.put(task + '.argv', ('\n'.join(args) + '\n').encode())
            rss = self.rss(task + '.rss', 10)
            selectors = self.receipt(task + '.selectors', **{key: 'absent' for key in ['SIMPLE_BOOTSTRAP', 'SIMPLE_NATIVE_BUILD_RUST', 'SIMPLE_BOOTSTRAP_STAGE3', 'SIMPLE_BOOTSTRAP_STAGE4', 'SIMPLE_BOOTSTRAP_WHOLE_PROGRAM', 'SIMPLE_TEST_RUNNER_RUST']})
            receipts[key] = self.receipt(task + '.env', selector_environment_path=selectors, selector_environment_sha256=e.sha(selectors), schema='simple-phase-verification-command-v1', task=task,
                status=0, source_root=self.root, artifact_path=self.cli, artifact_sha256=e.sha(self.cli),
                log_path=log, log_sha256=e.sha(log), argv_path=argv, argv_sha256=e.sha(argv), rss_receipt_path=rss, rss_receipt_sha256=e.sha(rss))
        for key, path in dict(self_result=self.r, selected_sanity=self.sg, command_owner=cmd, tooling_owner=tools,
                              runtime_capsule_receipt=cap, controller=controller, helper=helper,
                              evidence_validator=str(Path(e.__file__)), essential_tools_owner=owner, **receipts).items():
            fields[key + '_path'] = path; fields[key + '_sha256'] = e.sha(path)
        return self.receipt('cli.provenance.env', **fields)

    def test_candidate_and_changed_tool_rejection(self):
        c = self.candidate()
        # The separately tested existing capsule owner is the only external
        # verifier stub; no synthetic executable or owner is ever launched.
        with patch.object(e.subprocess, 'run') as capsule_verify:
            e.verify_candidate(c, self.cli, self.root)
            self.assertEqual(capsule_verify.call_count, 1)
            Path(self.runner).write_bytes(b'replaced runner')
            with self.assertRaises(ValueError): e.verify_candidate(c, self.cli, self.root)

    def test_rehashed_wrong_hello_runtime_is_rejected(self):
        g = e.env(self.sg); rp = str(Path(self.sg).parent / 'p3-hello-build.env'); rr = e.env(rp)
        tr = Path(rr['transcript_path'])
        tr.write_text(tr.read_text().replace(self.original, self.original[:-1] + 'X'))
        rr['transcript_sha256'] = e.sha(str(tr))
        Path(rp).write_text(''.join(k + '=' + v + '\n' for k, v in rr.items()))
        g['hello_build_receipt_sha256'] = e.sha(rp)
        Path(self.sg).write_text(''.join(k + '=' + v + '\n' for k, v in g.items()))
        with self.assertRaisesRegex(ValueError, 'DYLD_LIBRARY_PATH'): self.check()

    def test_optional_runtime_copy_must_equal_original(self):
        c = self.candidate()
        self.put('runtime-generation/libsimple_runtime.dylib', b'original')
        self.put('capsule/libsimple_runtime.dylib', b'changed')
        with patch.object(e.subprocess, 'run'):
            with self.assertRaisesRegex(ValueError, 'optional runtime copy changed'):
                e.verify_candidate(c, self.cli, self.root)

    def test_false_smoke_rejected_after_digest_rebinding(self):
        c = self.candidate(); d = e.env(c); sr = e.env(d['smoke_receipt_path'])
        Path(sr['log_path']).write_text('bootstrap_essential_tools_smoke=true\n')
        sr['log_sha256'] = e.sha(sr['log_path'])
        Path(d['smoke_receipt_path']).write_text(''.join(k + '=' + v + '\n' for k, v in sr.items()))
        d['smoke_receipt_sha256'] = e.sha(d['smoke_receipt_path']); d['essential_tools_log_sha256'] = e.sha(sr['log_path'])
        Path(c).write_text(''.join(k + '=' + v + '\n' for k, v in d.items()))
        with patch.object(e.subprocess, 'run'):
            with self.assertRaisesRegex(ValueError, 'smoke verdict'): e.verify_candidate(c, self.cli, self.root)


if __name__ == '__main__':
    unittest.main()

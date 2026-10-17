#!/usr/bin/env python3
"""Synthetic selection and scheduler evidence; never compiler qualification."""
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
CAMPAIGN = ROOT / 'scripts/bootstrap/bootstrap-verification-campaign.shs'
PROGRESS = ROOT / 'scripts/bootstrap/bootstrap-module-progress.py'
COLLECTION = ROOT / 'scripts/bootstrap/bootstrap-module-collection.shs'

class FullInventorySelection(unittest.TestCase):
    def limit(self, strategy, profile, fail_fast, configured='8', success=True):
        result = subprocess.run(['sh', '-c', '. "$1"; bootstrap_verification_module_limit "$2" "$3" "$4" "$5"', 'test', str(CAMPAIGN), strategy, profile, fail_fast, configured], capture_output=True, text=True)
        if success:
            self.assertEqual(result.returncode, 0, result.stderr)
            return result.stdout.strip()
        self.assertEqual(result.returncode, 2)

    def test_policy_modes(self):
        for strategy, profile in [('full', 'full'), ('normal', 'full')]:
            self.assertEqual(self.limit(strategy, profile, '0'), '0')
            self.assertEqual(self.limit(strategy, profile, '0', '3'), '0')
            self.assertEqual(self.limit(strategy, profile, '1'), '8')
        self.assertEqual(self.limit('normal', 'slim', '0'), '8')
        self.assertEqual(self.limit('normal', 'slim', '0', '3'), '3')
        self.assertEqual(self.limit('normal', 'slim', '0', '0'), '0')
        for arguments in [('bad','full','0','8'), ('full','bad','0','8'), ('full','full','bad','8'), ('full','full','0','-1')]:
            self.limit(*arguments, success=False)

    def test_failed_tools_do_not_truncate_full_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            inventory = work/'inventory'; selected = work/'selected'; summary = work/'summary'
            entries = [f'src/example/module_{index:05d}.spl' for index in range(14133)]
            inventory.write_text('\n'.join(entries)+'\n')
            limit = self.limit('full','full','0')
            # Exercise the actual shell selector with both tools unavailable.
            command = '. "$1"; bootstrap_verification_select_modules "$2" "$3" 0 0 "$4" "$5"'
            subprocess.run(['sh','-c',command,'test',str(CAMPAIGN),str(inventory),str(selected),limit,str(summary)], check=True)
            self.assertEqual(selected.read_text().splitlines(), entries)
            self.assertIn('module_compile_unexecuted_count=0\n', summary.read_text())
            # Exact old symptom remains available only for explicit checkpoint mode.
            subprocess.run(['sh','-c',command,'test',str(CAMPAIGN),str(inventory),str(selected),'8',str(summary)], check=True)
            self.assertEqual(len(selected.read_text().splitlines()),8)
            state = work/'state'; state.mkdir(); context = 'a'*64; target='aarch64-unknown-linux-gnu'
            rows=[]
            for index,entry in enumerate(entries[:8]):
                log=work/f'{index}.log'; log.write_text('synthetic failure\n' if index==0 else 'synthetic object\n')
                obj=work/f'{index}.o'; header=bytearray(20);header[:6]=b'\x7fELF\x02\x01';header[16:20]=b'\x01\x00\xb7\x00';obj.write_bytes(header)
                row=work/f'{index}.row';row.write_text(f'entry={entry}|result={"FAIL" if index==0 else "PASS"}|status={1 if index==0 else 0}|log={log}|artifact={obj}\n');rows.append(str(row))
            subprocess.run(['python3',str(PROGRESS),'publish',str(state),context,target,*rows],check=True)
            # The retained failed row keeps exit 3; all 14,125 unattempted rows
            # are selected. Seven synthetic PASS seals are not rebuilt.
            result=subprocess.run(['sh','-c','MODULE_PROGRESS_STATE=$6 MODULE_PROGRESS_HELPER=$7 MODULE_PROGRESS_CONTEXT=$8 MODULE_PROGRESS_TARGET=$9; . "$1"; bootstrap_verification_select_modules "$2" "$3" 0 0 "$4" "$5"','test',str(CAMPAIGN),str(inventory),str(selected),limit,str(summary),str(state),str(PROGRESS),context,target])
            self.assertEqual(result.returncode,3)
            self.assertEqual(selected.read_text().splitlines(),entries[8:])
            self.assertEqual(len(list(state.glob('*.json'))),8)
            self.assertIn('module_compile_retained_failed_count=1\n',summary.read_text())
            self.assertEqual(Path(str(selected)+'.unexecuted').read_text(),'')

    def test_scheduler_continues_after_failure_and_preserves_authority(self):
        with tempfile.TemporaryDirectory() as tmp:
            work=Path(tmp); manifest=work/'inventory';manifest.write_text('\n'.join(f'src/{i}.spl' for i in range(12))+'\n')
            obj=work/'synthetic.o';header=bytearray(20);header[:6]=b'\x7fELF\x02\x01';header[16:20]=b'\x01\x00\xb7\x00';obj.write_bytes(header)
            script='''set -u
. "$1"
work=$2
hash_stream() { sha256sum | awk '{print $1}'; }
validate() { [ "${authority_ok:-1}" = 1 ]; }
compile() { printf '%s\\n' "$1" >>"$work/executed"; [ "$1" != src/0.spl ] || return 1; cp "$work/synthetic.o" "$3"; }
SIMPLE_COMPILE_FAIL_FAST=0 MODULE_COMPILE_PRIOR_FAILURE=1
status=0
run_module_compile_inventory "$work/inventory" "$work/rows" "$work/cache" 2 1 compile validate "$work/summary" || status=$?
[ "$status" = 1 ] && [ "$(wc -l <"$work/executed")" = 12 ] || exit 10
grep -q 'entry=src/11.spl|result=PASS' "$work/summary" || exit 11
# Invalid authority must not run any compiler, even under keep-going.
authority_ok=0
run_module_compile_inventory "$work/inventory" "$work/blocked" "$work/cache" 2 1 compile validate "$work/blocked-summary" && exit 12
[ "$(wc -l <"$work/executed")" = 12 ] || exit 13
# Prior failed binary under fail-fast suppresses the whole selected queue.
authority_ok=1 SIMPLE_COMPILE_FAIL_FAST=1
run_module_compile_inventory "$work/inventory" "$work/skipped" "$work/cache" 2 1 compile validate "$work/skipped-summary" && exit 14
[ "$(wc -l <"$work/executed")" = 12 ] || exit 15
'''
            result=subprocess.run(['sh','-c',script,'test',str(COLLECTION),str(work)],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    unittest.main()

#!/usr/bin/env python3
"""Tiny fork/tool/shell/exec control for debugger transport, not compiler proof."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

root = Path('source/build/unit-observer-control').resolve()
root.mkdir(exist_ok=False)
c = root/'control.c'
c.write_text(r'''
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#define F compiler__hir__hir_lowering__module_surface_registry__ModuleSurfaceBuilder_dot_finish_into
#define G compiler__hir__hir_lowering__module_surface_registry_index__module_surfaces_freeze
#define P compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote_reason
volatile int observed = 0;
__attribute__((noinline)) void G(void) { observed++; }
__attribute__((noinline)) void F(void) { G(); observed++; }
__attribute__((noinline)) void P(void) { observed++; }
int main(int argc, char **argv) {
  if (argc == 2 && !strcmp(argv[1], "--worker")) {
    F(); P(); puts("UNEXPECTED_AFTER_PROMOTION"); return 9;
  }
  pid_t child = vfork(); int status;
  if (child == 0) { execl("/bin/true", "true", (char*)0); _exit(90); }
  if (child < 0 || waitpid(child,&status,0) < 0 || status != 0) return 91;
  child = vfork();
  if (child == 0) {
    execl("/bin/sh", "sh", "-c", "exec \"$0\" --worker", argv[0], (char*)0); _exit(92);
  }
  if (child < 0 || waitpid(child,&status,0) < 0) return 93;
  return 94;
}
''')
binary = root/'control'
subprocess.run(['cc', '-O0', '-g', str(c), '-o', str(binary)], check=True)
config = {'observer_control_only': True, 'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
          'required_worker_arg': '--worker', 'queue': str(root/'queue'), 'targets': [],
          'snapshot': str(root), 'events': str(root/'boundaries.jsonl')}
(root/'config.json').write_text(json.dumps(config))
env = dict(os.environ, UNIT_DIAGNOSTIC_CONFIG=str(root/'config.json'))
command = ['perl', str(Path('source/scripts/resource/process-tree-rss-watchdog.pl').resolve()),
           '--rss-cap-mode=enforce', '--max-rss-kib=524288', '--timeout-seconds=20',
           '--receipt='+str(root/'owner.env'), '--', 'gdb', '-q', '-batch',
           '-ex', 'set pagination off', '-ex', 'set confirm off', '-ex', 'set disable-randomization off',
           '-ex', 'source '+str(Path(__file__).with_name('full-cli-unit-memory-gdb.py').resolve()),
           '--args', str(binary)]
with (root/'stdout').open('wb') as out, (root/'stderr').open('wb') as err:
    code = subprocess.run(command, env=env, stdout=out, stderr=err).returncode
events = [json.loads(x) for x in (root/'boundaries.jsonl').read_text().splitlines()]
stages = [x['stage'] for x in events if x.get('comparable')]
owner = dict(x.split('=',1) for x in (root/'owner.env').read_text().splitlines() if '=' in x)
assert code == 0 and owner['status'] == 'complete' and owner['quiescent'] == '1' and owner['rss_cap_enforced'] == '1'
assert stages == ['finish:entry','freeze:entry','freeze:return','finish:return','promote:entry','promote:return']
assert 'UNEXPECTED_AFTER_PROMOTION' not in (root/'stdout').read_text()
assert len({x['pid'] for x in events}) == 1
(root/'result.json').write_text(json.dumps({'observer_control_only': True, 'status': 'PASS', 'stages': stages}))

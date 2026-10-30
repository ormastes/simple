"""Focused authority-binding negatives; no compiler/process launch or qualification."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if os.name!='nt':
        raise SystemExit('Windows native ownership helper test requires Windows')
    args.output.mkdir(parents=True,exist_ok=False)
    owner=Path(__file__).resolve().parents[1]/'bootstrap/owned_worker_wall_drain_windows.py'
    spec=importlib.util.spec_from_file_location('drain_owner',owner)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    body=args.output/'fixture-workload.spec'
    body.write_bytes(b'FIXTURE immutable workload, never compiler authority\0')
    argv=args.output/'fixture-argv.sdn'
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    base=['fixture-watchdog','--timeout-seconds=60','--rss-cap-mode=monitor','--',sys.executable,'fixture-collector','--timeout-seconds','60','--max-bytes','8388608','--root-exit-policy','wait-job','--',sys.executable,'FIXTURE-parent']
    def plan_for(values):
        argv.write_text('schema: binding-negative-FIXTURE-v1\nargv: [\n'+''.join('  '+json.dumps(x)+',\n' for x in values)+']\n')
        return {'workload_spec_path':str(body),'workload_spec_sha256':sha(body),'launch_argv_path':str(argv),'launch_argv_sha256':sha(argv),'outer_wall_seconds':'60','parent_image':sys.executable.replace('\\','/')}
    def rejected(plan):
        try:module.validate_launch_binding(plan)
        except (ValueError,KeyError,IndexError):return
        raise AssertionError('invalid binding accepted')
    plan=plan_for(base);module.validate_launch_binding(plan)
    rejected(dict(plan,workload_spec_sha256='0'*64))
    rejected(dict(plan,launch_argv_sha256='0'*64))
    rejected(dict(plan,outer_wall_seconds='3600'))
    rejected(dict(plan,parent_image='C:/FIXTURE-foreign.exe'))
    for before,after in [('--timeout-seconds=60','--timeout-seconds=0'),('--rss-cap-mode=monitor','--rss-cap-mode=enforce'),('8388608','16777216'),('wait-job','terminate-job')]:
        rejected(plan_for([after if x==before else x for x in base]))
    changed=list(base);changed[changed.index('--timeout-seconds')+1]='61';rejected(plan_for(changed))
    rejected(plan_for(base+['--timeout-seconds','60']))
    plan=plan_for(base);body.write_bytes(b'changed source bytes\0');rejected(plan)
    guard_plan={'outer_deadline_utc':'2026-10-25T11:40:30Z','outer_wall_seconds':'60'}
    created=module.utc_ns('2026-10-25T11:39:30Z')//100+116444736000000000
    module.validate_guard_deadline(guard_plan,created)
    guard_plan['outer_deadline_utc']='2026-10-25T11:40:31Z'
    try:module.validate_guard_deadline(guard_plan,created)
    except ValueError:pass
    else:raise AssertionError('deadline exceeding actual native guard lifetime accepted')
    (args.output/'verification.sdn').write_text('schema: owned-worker-drain-binding-verification-v1\nstatus: PASS\nqualification: authority-validator-FIXTURE-no-process-actions\npositive_bindings: 1\nnegative_bindings: 11\nguard_lifetime_positive_and_negative: PASS\nhelper_sha256: '+sha(owner)+'\ncompiler_qualification: NONE\n')
    print('PASS authority binding and guard lifetime controls; no processes launched')

if __name__=='__main__':main()

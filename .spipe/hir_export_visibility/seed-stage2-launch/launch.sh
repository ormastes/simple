#!/bin/sh
# Disabled until root records explicit user authorization for ONE budget exception.
set -eu
ROOT=/home/yoon/dev/simple-seed-stage2-exception-20261107
META="$ROOT/.spipe/seed_stage2_exception"
RUN="$ROOT/build/seed-stage2-exception"
cd "$ROOT"
python3 - "$ROOT" "$META" "$RUN" "$0" <<'PY_PREFLIGHT'
import sys,json,hashlib,subprocess,os,shutil
from pathlib import Path
root,meta,run,script=map(Path,sys.argv[1:])
def read(p):
 return {k:json.loads(v) for k,v in (l.split(': ',1) for l in p.read_text().splitlines())}
pins=read(meta/'source-inputs.sdn')
enable=read(meta/'root-enable.sdn') # Absent by design until explicit approval.
assert enable=={'source_commit':pins['source_commit'],'launcher_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),'user_authorized_budget_exception':True,'max_cores':5,'rss_cap_kib':50331648,'wall_seconds':43200,'minimum_free_gib':32},'authorization mismatch'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==pins['source_commit']
assert not subprocess.check_output(['git','diff','--name-only','HEAD'],text=True),'tracked source modified'
for path,key in [('scripts/bootstrap/run-process-group-timeout.shs','guard_sha256'),('scripts/bootstrap/bootstrap-from-scratch.sh','bootstrap_sha256')]:
 assert hashlib.sha256((root/path).read_bytes()).hexdigest()==pins[key]
assert hashlib.sha256((meta/'host.sdn').read_bytes()).hexdigest()==pins['host_config_sha256']
assert not (root/'src/compiler_rust/target').exists(),'private seed authority already exists'
assert not run.exists(),'output already exists'
for row in subprocess.check_output(['git','ls-files','-s'],text=True).splitlines():
 if row.startswith('120000 '):
  name=row.split('\t',1)[1]
  if name.startswith(('src/','examples/','scripts/')):assert (root/name).resolve(strict=True).is_relative_to(root)
assert set(range(5)).issubset(os.sched_getaffinity(0)),'requested CPUs unavailable'
assert shutil.disk_usage(root).free>=32*1024**3,'less than32GiB free'
mem={l.split(':')[0]:int(l.split()[1]) for l in Path('/proc/meminfo').read_text().splitlines()}
assert mem['MemAvailable']>=50331648+25165824 and 50331648<=mem['MemAvailable']*3//4,'host reserve/75percent refusal'
(meta/'consumed').mkdir() # One-use latch, no automatic retry.
run.mkdir()
for name in ['tmp','cargo-cache','native','frontend','hir','user-storage','worktree-storage']:(run/name).mkdir()
PY_PREFLIGHT
set +e
taskset -c 0-4 env -i  PATH=/home/yoon/dev/llvm/install/bin:/home/yoon/.cargo/bin:/usr/local/bin:/usr/bin:/bin  HOME="$HOME" RUSTUP_HOME=/home/yoon/.rustup  SIMPLE_ABI_POLICY=v1 LLVM_SYS_231_PREFIX=/home/yoon/dev/llvm/install  SIMPLE_TOOLCHAINS_ROOT=/home/yoon/.simple/toolchains  SIMPLE_HOST_CONFIG="$META/host.sdn"  SIMPLE_USER_STORAGE_ROOT="$RUN/user-storage"  SIMPLE_WORKTREE_STORAGE_ROOT="$RUN/worktree-storage"  SIMPLE_BOOTSTRAP_RUST_CARGO_CACHE_ROOT="$RUN/cargo-cache"  SIMPLE_NATIVE_BUILD_CACHE_DIR="$RUN/native"  SIMPLE_FRONTEND_CACHE_DIR="$RUN/frontend" SIMPLE_HIR_CACHE_DIR="$RUN/hir"  SIMPLE_CACHE="$RUN/user-storage/cache/compiler/bootstrap/v1/cas"  TMPDIR="$RUN/tmp"  SIMPLE_PROCESS_TREE_RSS_CAP_KIB=50331648  SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=50331648  SIMPLE_BOOTSTRAP_RSS_CAP_MODE=enforce  SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP=0  SIMPLE_PROCESS_TREE_RSS_RECEIPT="$RUN/process.env"  SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS=1  SIMPLE_BOOTSTRAP_MIN_FREE_GB=32 MIN_FREE_GB=32  SIMPLE_NATIVE_BUILD_THREADS=1 CARGO_BUILD_JOBS=1  sh scripts/bootstrap/run-process-group-timeout.shs 43200 15  sh scripts/bootstrap/bootstrap-from-scratch.sh  --full-bootstrap --stop-after-stage2 --mode=dynload --backend=llvm  --jobs=1 --fail-fast --output="$RUN/output" >"$RUN/build.log" 2>&1
code=$?
set -e
python3 - "$ROOT" "$META" "$RUN" "$code" <<'PY_RESULT'
import sys,json,subprocess,hashlib
from pathlib import Path
root,meta,run=map(Path,sys.argv[1:4]);code=int(sys.argv[4]);receipt={}
if (run/'process.env').exists():receipt=dict(l.split('=',1) for l in (run/'process.env').read_text().splitlines() if '=' in l)
unchanged=not subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=root,text=True)
result={'status':'terminal-root-review-required','exit_status':code,'quiescent':receipt.get('quiescent','missing'),'source_unchanged':unchanged,'log_sha256':hashlib.sha256((run/'build.log').read_bytes()).hexdigest(),'automatic_retry':False,'additional_stage_authorized':False}
(meta/'result.sdn').write_text(''.join(k+': '+json.dumps(v)+'\n' for k,v in result.items()))
print(json.dumps(result))
sys.exit(0 if code==0 and receipt.get('quiescent')=='1' and unchanged else 1)
PY_RESULT

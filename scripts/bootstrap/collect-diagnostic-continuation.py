#!/usr/bin/env python3
"""Preserve bounded, explicitly unadmitted bootstrap continuation inputs."""
import hashlib,json,os,pathlib,shutil,sys
root=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[2]).resolve();budget=int(sys.argv[3])
if budget<=0 or out.exists():raise SystemExit('refuse invalid budget or existing output')
out.mkdir(parents=True);rows=[];used=0;excluded=[]
roots=['build/bootstrap','.simple/storage/build/bootstrap','src/compiler_rust/target/bootstrap']
candidates=[]; root_status=[]; rejected=[]
for rel in roots:
 base=root/rel
 if not base.exists():root_status.append({'path':rel,'present':False});continue
 if base.resolve()!=base or not base.resolve().is_relative_to(root) or any(x.is_symlink() for x in [base,*list(base.parents)[:len(pathlib.Path(rel).parts)-1]]):
  root_status.append({'path':rel,'present':True,'rejected':'symlink_or_escape'});rejected.append({'path':rel,'reason':'symlink_or_escape'});continue
 root_status.append({'path':rel,'present':True})
 for parent,dirs,files in os.walk(base,followlinks=False,onerror=lambda error: rejected.append({'path':str(error.filename),'reason':str(error)})):
  dirs[:]=sorted(d for d in dirs if not (pathlib.Path(parent)/d).is_symlink() and d not in ['incremental','.fingerprint','build'])
  for name in sorted(files):
   p=pathlib.Path(parent)/name;relative=p.relative_to(root).as_posix()
   try:
    metadata=p.lstat()
    if p.is_symlink():rejected.append({'path':relative,'reason':'source_symlink'});continue
    if not p.is_file():continue
   except OSError as error:
    rejected.append({'path':relative,'reason':str(error)});continue
   binary=name in ['simple','simple.exe','simple.rejected','simple.exe.rejected']
   archive=name in ['libsimple_native_all.a','libsimple_compiler_backfill.a','simple_native_all.lib','simple_compiler_backfill.lib']
   cache_owner=any(part in ['native_cache','stage2-native-cache','stage3-native-cache'] for part in pathlib.PurePosixPath(relative).parts)
   cache=cache_owner and (p.suffix in ['.o','.obj','.env','.json','.sdn','.manifest'] or name in ['.cache_scope','incremental_manifest.txt'])
   metadata=not relative.startswith('src/compiler_rust/target/') and p.suffix in ['.env','.json','.manifest','.sdn']
   if binary or archive or cache or metadata:candidates.append((0 if binary else 1 if archive else 2 if metadata else 3,p,relative))
for _,p,relative in sorted(candidates,key=lambda x:(x[0],x[2])):
 try:
  size=p.lstat().st_size
 except OSError as error:
  rejected.append({'path':relative,'reason':str(error)});continue
 if size>budget-used:excluded.append({'path':relative,'size':size,'reason':'budget'});continue
 h=hashlib.sha256();target=out/'files'/relative;copied=0
 try:
  target.parent.mkdir(parents=True,exist_ok=True)
  before=p.lstat();
  if p.is_symlink():raise ValueError('source_symlink')
  identity=(before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)
  with os.fdopen(os.open(p,os.O_RDONLY | getattr(os,'O_NOFOLLOW',0)), 'rb') as src,target.open('xb') as dst:
   opened=os.fstat(src.fileno())
   if (opened.st_dev,opened.st_ino,opened.st_size,opened.st_mtime_ns)!=identity:raise ValueError('source_changed_before_copy')
   while True:
    chunk=src.read(min(1024*1024,budget-used-copied+1))
    if not chunk:break
    if copied+len(chunk)>budget-used:raise ValueError('actual_bytes_exceed_budget')
    h.update(chunk);dst.write(chunk);copied+=len(chunk)
   after=os.fstat(src.fileno());published=p.lstat()
   if (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns)!=identity or (published.st_dev,published.st_ino,published.st_size,published.st_mtime_ns)!=identity or copied!=before.st_size:raise ValueError('source_changed_during_copy')
  shutil.copystat(p,target,follow_symlinks=False)
 except (OSError,ValueError) as error:
  target.unlink(missing_ok=True);rejected.append({'path':relative,'reason':str(error),'copied_bytes_discarded':copied});continue
 used+=copied;rows.append({'path':relative,'size':copied,'sha256':h.hexdigest()})
receipt={'schema':'bootstrap-diagnostic-continuation-v1','admission':'UNADMITTED','source_sha':os.environ.get('GITHUB_SHA','unknown'),'run_id':os.environ.get('GITHUB_RUN_ID','local'),'budget_bytes':budget,'preserved_bytes':used,'selection_complete':not excluded and not rejected,'coverage':'selected continuation inputs only; not full build/cache completeness','canonical_roots':root_status,'rejected':rejected,'compiler_present':any(pathlib.Path(x['path']).name in ['simple','simple.exe','simple.rejected','simple.exe.rejected'] for x in rows),'runtime_archives_present':all(any(pathlib.Path(x['path']).name in names for x in rows) for names in [['libsimple_native_all.a','simple_native_all.lib'],['libsimple_compiler_backfill.a','simple_compiler_backfill.lib']]),'files':rows,'excluded':excluded}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(f'diagnostic_artifacts files={len(rows)} bytes={used} excluded={len(excluded)} admission=UNADMITTED')

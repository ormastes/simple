"""Project the exact prior qualified parent, excluding its optional Hello cache.

This does not rerun or invent qualification. Every retained byte is verified
against the original sealed manifest; missing non-cache bytes are fatal.
"""
import argparse,hashlib,importlib.util,json,pathlib,stat,subprocess,zipfile
P=pathlib.Path
s=importlib.util.spec_from_file_location('control',P(__file__).with_name('control.py'));c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
PRIOR_RUN=45337338360
PRIOR_HEAD='5f08230a707dbfb0291db381a1c20f6bf7473ace'
ARTIFACT=14894636550;SIZE=113732849
DIGEST='f09d729c89679a7ba94dab06e20e6f7d794b382be889c80c0555423ddffe1160'
CACHE='parent-native-hello/cache/'
MISSING='parent-native-hello/cache/native-build/v1/default/hir/.by-source/c88dbb52a198f3eb.idx'
def safe(name):
 p=pathlib.PurePosixPath(name)
 assert name and str(p)==name and not p.is_absolute() and '..' not in p.parts
 assert '\\' not in name and ':' not in name and '\x00' not in name
 return p
def project(archive,out,api_evidence=None):
 assert archive.stat().st_size==SIZE and c.sha(archive)==DIGEST
 out.mkdir(parents=True,exist_ok=False)
 with zipfile.ZipFile(archive) as z:
  names={};folded=set()
  for item in z.infolist():
   safe(item.filename);assert not item.is_dir() and not stat.S_ISLNK(item.external_attr>>16)
   assert item.filename.casefold() not in folded;folded.add(item.filename.casefold());names[item.filename]=item
  raw=z.read('files.json');original=json.loads(raw)
  for name in original:safe(name)
  assert set(names)-set(original)=={'files.json'}
  missing=sorted(set(original)-set(names));assert missing==[MISSING]
  for name,digest in original.items():
   if name in names:assert hashlib.sha256(z.read(name)).hexdigest()==digest,name
  retained={name:digest for name,digest in original.items() if not name.startswith(CACHE)}
  assert all(name in names for name in retained)
  for name,digest in retained.items():
   target=out.joinpath(*safe(name).parts);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(name))
   target.chmod(0o755 if (names[name].external_attr>>16)&0o111 else 0o644)
   assert c.sha(target)==digest
  (out/'transfer-original-files.json').write_bytes(raw)
 parent=json.loads((out/'parent.json').read_text());q=json.loads((out/'parent-native-hello/qualification.json').read_text())
 assert parent['status']=='QUALIFIED_PROVISIONAL_PARENT' and parent['source']==c.SOURCE and parent['original_run']==c.RUN
 assert parent['fresh_hello']==q and q['status']=='BEHAVIOR_PASS' and q['role']=='parent' and q['source']==c.SOURCE
 binary=out/'parent/simple_stage2';hello=out/'parent-native-hello/hello';c.elf(binary);c.elf(hello)
 assert c.sha(binary)==parent['parent_sha256']==q['product_sha256']
 assert q['claims']['native_hello'] and c.sha(hello)==q['claims']['native_hello_sha256']
 assert (out/'parent-native-hello/native-hello-run.stdout').read_bytes()==b'hello\n'
 for name,digest in parent['runtime_files'].items():assert c.sha(out/'runtime'/name)==digest
 for name,digest in q['runtime_files'].items():assert c.sha(out/'runtime'/name)==digest
 for label,cap,seconds in [('native-hello-build',4194304,600),('native-hello-run',262144,30)]:
  receipt=dict(x.split('=',1) for x in (out/('parent-native-hello/'+label+'.owner.env')).read_text().splitlines() if '=' in x)
  assert receipt['status']=='complete' and receipt['exit_status']=='0' and receipt['quiescent']==receipt['rss_cap_enforced']=='1'
  assert int(receipt['rss_limit_kib'])==cap
  argv=json.loads((out/('parent-native-hello/'+label+'.argv.json')).read_text())
  assert '--max-rss-kib='+str(cap) in argv and '--timeout-seconds='+str(seconds) in argv
  child=argv[argv.index('--')+1:]
  if label.endswith('build'):
   assert child[0].endswith('/qualified-parent/parent/simple_stage2') and child[1]=='native-build'
   for value in ['llvm','x86_64-unknown-linux-gnu','core-c-bootstrap','test/04_smoke/bootstrap_hello_world.spl']:assert value in child
  else:assert len(child)==1 and child[0].endswith('/qualified-parent/parent-native-hello/hello')
 receipt={'status':'VERIFIED_PROJECTION','prior_run':PRIOR_RUN,'prior_control':PRIOR_HEAD,'artifact_id':ARTIFACT,'archive_sha256':DIGEST,'original_manifest_sha256':hashlib.sha256(raw).hexdigest(),'original_count':len(original),'missing':missing,'excluded_cache_count':sum(n.startswith(CACHE) for n in original),'retained_count':len(retained),'scope':'original successful native Hello evidence retained, no execution; optional cache omitted entirely','mode_policy':'original executable bits restored on projection; child and trueP4 explicitly chmod their selected compiler0755 after ZIP transport'}
 c.save(out/'transfer-projection.json',receipt)
 if api_evidence is not None:c.save(out/'transfer-api.json',api_evidence)
 c.save(out/'files.json',{str(p.relative_to(out)).replace('\\','/'):c.sha(p) for p in out.rglob('*') if p.is_file()})
 sealed=json.loads((out/'files.json').read_text());actual={str(p.relative_to(out)).replace('\\','/') for p in out.rglob('*') if p.is_file()}
 assert actual==set(sealed)|{'files.json'} and all(c.sha(out/n)==h for n,h in sealed.items())
 return receipt
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=P,required=True);p.add_argument('--archive',type=P);p.add_argument('--artifact-pins');a=p.parse_args()
 api_evidence=None
 if a.archive is None:
  c.source_guard(P('source'))
  run=c.api('actions/runs/'+str(PRIOR_RUN));assert run['head_sha']==PRIOR_HEAD and run['event']=='workflow_dispatch'
  jobs=c.api('actions/runs/'+str(PRIOR_RUN)+'/jobs?per_page=100')['jobs']
  intake=next(j for j in jobs if j['name']=='intake');assert intake['status']=='completed' and intake['conclusion']=='success'
  meta=c.api('actions/artifacts/'+str(ARTIFACT));assert not meta['expired'] and meta['workflow_run']['id']==PRIOR_RUN and meta['workflow_run']['head_sha']==PRIOR_HEAD
  assert meta['name']=='qualified-656fa39e-parent-'+str(PRIOR_RUN) and meta['digest']=='sha256:'+DIGEST and meta['size_in_bytes']==SIZE
  a.archive=P('prior-qualified-parent.zip')
  with a.archive.open('xb') as f:subprocess.run(['gh','api','repos/'+c.REPO+'/actions/artifacts/'+str(ARTIFACT)+'/zip'],stdout=f,check=True,timeout=600)
  api_evidence={'run':run,'intake_job':intake,'artifact':meta}
 result=project(a.archive,a.output,api_evidence)
 if a.artifact_pins:assert json.loads(a.artifact_pins)==json.loads((a.output/'parent.json').read_text())['artifact_pins']
 print(json.dumps(result))
if __name__=='__main__':main()

"""One true Phase4 product from an immutable, genuinely successful Phase3 archive."""
import argparse,importlib.util,json,stat,subprocess,zipfile
from pathlib import Path,PurePosixPath
s=importlib.util.spec_from_file_location('control',Path(__file__).with_name('control.py'));c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
CONTROL='5f08230a707dbfb0291db381a1c20f6bf7473ace'
BRANCH='work/linux-656fa39e-children-20261124'
def unpack(number,digest,run,name,out):
 meta=c.api('actions/artifacts/'+str(number))
 assert not meta['expired'] and meta['name']==name and meta['digest']=='sha256:'+digest
 assert meta['workflow_run']['id']==run and meta['workflow_run']['head_sha']==CONTROL
 archive=out.with_suffix('.zip')
 with archive.open('wb') as f:subprocess.run(['gh','api','repos/'+c.REPO+'/actions/artifacts/'+str(number)+'/zip'],stdout=f,check=True,timeout=1200)
 assert archive.stat().st_size==meta['size_in_bytes'] and c.sha(archive)==digest
 out.mkdir();seen=set()
 with zipfile.ZipFile(archive) as z:
  for item in z.infolist():
   p=PurePosixPath(item.filename);key=str(p).casefold()
   assert not p.is_absolute() and '..' not in p.parts and '\\' not in item.filename and ':' not in item.filename and '\x00' not in item.filename
   assert key not in seen and not stat.S_ISLNK(item.external_attr>>16);seen.add(key)
   dest=out.joinpath(*p.parts)
   if item.is_dir():dest.mkdir(parents=True,exist_ok=True)
   else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(item))
 c.save(out.with_suffix('.artifact.json'),meta)
 return out
def gate(run,root):
 metadata=c.api('actions/runs/'+str(run))
 assert metadata['head_sha']==CONTROL and metadata['head_branch']==BRANCH and metadata['event']=='workflow_dispatch'
 jobs=c.api('actions/runs/'+str(run)+'/jobs?per_page=100')['jobs']
 job=next(j for j in jobs if j['name']=='New 656fa39e phase3')
 assert job['status']=='completed' and job['conclusion']=='success'
 assert next(s for s in job['steps'] if s['name']=='Independent provisional product owner and qualification')['conclusion']=='success'
 # An unrelated early-fullCLI sibling may still be running/failed. Only this
 # exact successful P3 and shared successful intake are dependencies.
 assert next(j for j in jobs if j['name']=='intake')['conclusion']=='success'
 c.save(root/'parent-run.json',metadata);c.save(root/'parent-job.json',job)
 artifacts=c.api('actions/runs/'+str(run)+'/artifacts?per_page=100')['artifacts']
 intake={}
 for kind,name in [('phase3','linux-656fa39e-phase3-'+str(run)),('qualified-parent','qualified-656fa39e-parent-'+str(run))]:
  found=[a for a in artifacts if a['name']==name];assert len(found)==1
  a=found[0];digest=a['digest'];assert digest.startswith('sha256:') and len(digest)==71
  intake[kind]={'id':a['id'],'sha256':digest[7:]}
 c.save(root/'artifact-intent.json',intake)
 p3=unpack(intake['phase3']['id'],intake['phase3']['sha256'],run,'linux-656fa39e-phase3-'+str(run),root/'phase3')
 prior=unpack(intake['qualified-parent']['id'],intake['qualified-parent']['sha256'],run,'qualified-656fa39e-parent-'+str(run),root/'qualified-parent')
 manifest=json.loads((prior/'files.json').read_text())
 for path,digest in manifest.items():assert c.sha(prior/path)==digest
 parent=json.loads((prior/'parent.json').read_text());assert parent['status']=='QUALIFIED_PROVISIONAL_PARENT' and parent['source']==c.SOURCE and parent['original_run']==c.RUN
 result=json.loads((p3/'terminal.json').read_text())
 assert result['status']=='BEHAVIOR_PASS' and result['role']=='phase3' and result['source']==c.SOURCE and result['immutable_inputs_after']=='PASS'
 assert result['parent_sha256']==parent['parent_sha256'] and result['runtime_files']==parent['runtime_files']
 policy=json.loads((p3/'resource-policy.json').read_text())
 owner=dict(x.split('=',1) for x in (p3/'build.owner.env').read_text().splitlines() if '=' in x)
 assert owner['status']=='complete' and owner['exit_status']=='0' and owner['quiescent']==owner['rss_cap_enforced']=='1'
 assert int(owner['rss_limit_kib'])==policy['cap_kib'] and policy['cap_kib']<=policy['available_kib']*3//4
 argv=json.loads((p3/'build.argv.json').read_text())
 for value in ('--timeout-seconds=18500','--max-rss-kib='+str(policy['cap_kib']),'--phase=p3a','--compile-mode=file','--backend=llvm','--target=x86_64-unknown-linux-gnu','--threads=2'):assert value in argv
 for key,suffix in (('--p2-bin=','/qualified-parent/parent/simple_stage2'),('--runtime-path=','/qualified-parent/runtime'),('--source-root=','/source'),('--build-root=','/child-evidence/phased')):
  matches=[v for v in argv if v.startswith(key)];assert len(matches)==1 and matches[0].endswith(suffix)
 assert argv[argv.index('--')+1:argv.index('--')+3]==['bash','scripts/bootstrap/build-phase3-phase4.sh']
 binary=p3/'phased/phase3-a/simple';hello=p3/'phased/phase3-a/hello'
 c.elf(binary);c.elf(hello/'hello')
 assert c.sha(binary)==result['product_sha256'] and c.sha(hello/'hello')==result['native_hello_sha256']
 assert (hello/'stdout').read_bytes()==(hello/'expected').read_bytes()==b'hello\n'
 assert (hello/'compile.log').is_file()
 runtime=prior/'runtime'
 for name,digest in parent['runtime_files'].items():assert c.sha(runtime/name)==digest
 # Entire product directory retained, including dynload companions; caches
 # remain evidence only and are not installed into this child's fresh cache.
 product_files={str(p.relative_to(p3/'phased/phase3-a')):c.sha(p) for p in (p3/'phased/phase3-a').rglob('*') if p.is_file()}
 proof={'status':'VERIFIED_PHASE3_PARENT','source':c.SOURCE,'parent_run':run,'parent_control_sha':CONTROL,'artifact_pins':intake,'phase2_sha256':parent['parent_sha256'],'phase3_sha256':c.sha(binary),'binary':str(binary),'runtime':str(runtime),'runtime_files':parent['runtime_files'],'product_files':product_files,'native_hello_sha256':result['native_hello_sha256'],'owner_sha256':c.sha(p3/'build.owner.env'),'scope':'real P3a native Hello revalidated from retained evidence; no rerun or formal admission'}
 c.save(root/'phase3-parent.json',proof);return proof
def main():
 p=argparse.ArgumentParser();p.add_argument('--parent-run',required=True,type=int);p.add_argument('--source',required=True,type=Path);p.add_argument('--intake',required=True,type=Path);p.add_argument('--output',required=True,type=Path);a=p.parse_args()
 a.intake=a.intake.resolve();a.intake.mkdir(parents=True,exist_ok=False)
 with (a.intake/'claim.json').open('x') as f:json.dump({'parent_run':a.parent_run,'control_sha':CONTROL},f)
 proof=gate(a.parent_run,a.intake)
 a.parent=a.intake;a.role='full-cli'
 try:c.child(a,proof)
 finally:
  base=Path(proof['binary']).parent
  unchanged=all(c.sha(base/name)==digest for name,digest in proof['product_files'].items())
  c.save(a.intake/'parent-unchanged.json',{'status':'PASS' if unchanged else 'FAIL','phase3_sha256':proof['phase3_sha256']})
  assert unchanged
if __name__=='__main__':main()

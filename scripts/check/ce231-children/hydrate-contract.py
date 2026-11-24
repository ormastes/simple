"""Intake only. Fetch verified terminal artifacts and hydrate a runnable Linux contract."""
import hashlib,json,os,stat,subprocess,zipfile
from pathlib import Path,PurePosixPath
SOURCE='ce231b5b898d797c98d44a9b59a4859a7d792a7b'
CONTROL='79f7e678d48d35e1319e12fdae52cea01d2e0352'
repo=os.environ['GITHUB_REPOSITORY']
root=Path('ce231-intake').resolve();root.mkdir(exist_ok=False)
def api(route):return json.loads(subprocess.check_output(['gh','api',f'repos/{repo}/'+route]))
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(name,data):
 p=root/name;p.write_text(json.dumps(data,indent=2));return str(p)
p2=api('actions/runs/45275222826');fd=api('actions/runs/45241703685')
assert p2['head_sha']==CONTROL and p2['status']=='completed' and p2['conclusion']=='success'
assert fd['status']=='completed' and fd['conclusion']!='success','fd366 not eligible for replacement'
def extract(artifact,dest,digest):
 assert not artifact['expired'] and artifact['digest']=='sha256:'+digest
 archive=root/(str(artifact['id'])+'.zip')
 with archive.open('wb') as f:subprocess.run(['gh','api',f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"],stdout=f,check=True)
 assert sha(archive)==digest
 dest.mkdir()
 with zipfile.ZipFile(archive) as z:
  names=set();size=0
  for item in z.infolist():
   p=PurePosixPath(item.filename)
   assert not p.is_absolute() and '..' not in p.parts and '\\' not in item.filename and ':' not in item.filename
   assert p.as_posix()==item.filename.rstrip('/') and p.as_posix().casefold() not in names
   names.add(p.as_posix().casefold())
   assert not stat.S_ISLNK(item.external_attr>>16)
   size+=item.file_size;assert size<40*1024**3
  # Parent native cache is not a child cache; retain the full ZIP but extract evidence/products only.
  for item in z.infolist():
   if '/cache/' not in '/'+item.filename: z.extract(item,dest)
 return str(archive)
arts=api('actions/runs/45275222826/artifacts')['artifacts']
selected=[x for x in arts if x['name']=='pinned-candidate-phase2-single-worker-45275222826'];assert len(selected)==1
pa=api('actions/artifacts/'+str(selected[0]['id']));assert pa['workflow_run']['id']==45275222826
pd=pa['digest'].removeprefix('sha256:');pz=extract(pa,root/'phase2',pd)
ra=api('actions/artifacts/14871469985');assert ra['workflow_run']['id']==45286831153
rz=extract(ra,root/'runtime','5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9')
terminals=[]
for p in (root/'phase2').rglob('terminal.json'):
 t=json.loads(p.read_text())
 if t.get('phase')==2 and t.get('source')==SOURCE and t.get('status')=='PASS':terminals.append((p,t))
assert len(terminals)==1
terminal,t=terminals[0]
producers=[p for p in (root/'phase2').rglob('simple') if p.is_file() and sha(p)==t['compiler_sha256']]
assert len(producers)==1;producer=producers[0];producer.chmod(0o755)
manifests=[p for p in (root/'runtime').rglob('manifest.json') if json.loads(p.read_text()).get('status')=='BUILT_UNQUALIFIED'];assert len(manifests)==1
manifest=json.loads(manifests[0].read_text());runtime=manifests[0].parent/'runtime'
assert manifest['source_revision']==SOURCE
c=json.loads((Path(__file__).parent/'combined-contract.pending.json').read_text())
c.update(phase2_artifact_id=pa['id'],phase2_artifact_zip_sha256=pd,phase2_artifact_zip=pz,
 phase2_producer=str(producer),phase2_producer_sha256=t['compiler_sha256'],phase2_terminal=str(terminal),
 phase2_terminal_sha256=sha(terminal),phase2_evidence_directory=str(terminal.parent),
 source_root=str(Path('source').resolve()),runtime_root=str(runtime),runtime_artifact_zip=rz,
 runtime_files={k:v['sha256'] for k,v in manifest['files'].items()},
 phase2_run_metadata=save('phase2-run.json',p2),fd366_run_metadata=save('fd366-run.json',fd),
 output_root=str(Path('ce231-children').resolve()),early_product=os.environ['EARLY_PRODUCT'],phase4_memory_kib=None)
save('phase2-artifact.json',pa);save('runtime-artifact.json',ra)
Path('ce231-contract.json').write_text(json.dumps(c,indent=2))

if c['early_product']=='mcp':
 blob=subprocess.check_output(['git','hash-object','src/app/mcp/main_lazy_protocol.spl'],cwd=c['source_root'],text=True).strip()
 assert blob=='060954507ec74e4efced6a14f6b59c14d79cacd6','MCP11124 prerequisite absent in ce231: select full-cli; never overlay sources'

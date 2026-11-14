from pathlib import Path
import collections,hashlib,re,subprocess,sys
repo=Path(__file__).resolve().parents[2]; out=Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=False);(out/'src').mkdir()
index=collections.defaultdict(list)
rows=subprocess.check_output(['git','grep','-n','-E',r'^(pub )?(struct|enum|class|type) [A-Za-z_][A-Za-z_0-9]*','--','src/compiler','src/lib/common','src/app/cli/bootstrap_focused_native_build_args.spl'],cwd=repo,text=True)
for row in rows.splitlines():
 path,line,text=row.split(':',2);name=re.match(r'(?:pub )?(?:struct|enum|class|type) (\w+)',text)[1];index[name].append(path)
cache={}
def read(path):
 if path not in cache:cache[path]=(repo/path).read_text()
 return cache[path]
def block(text,pattern,indent=' '):
 lines=text.splitlines(True);start=next(i for i,s in enumerate(lines) if re.match(pattern,s));end=start+1
 while end<len(lines) and (not lines[end].strip() or lines[end].startswith(indent)):end+=1
 return ''.join(lines[start:end])
def decl(path,name,kind='fn'):
 return block(read(path),r'(?:pub )?'+kind+' '+re.escape(name)+r'\b')
common='src/compiler/00.common/driver_compile_options.spl';mode='src/compiler/00.common/driver_core_modes.spl';args='src/app/cli/bootstrap_focused_native_build_args.spl';xray='src/compiler/80.driver/driver_xray_policy.spl';aspect='src/lib/common/plugin/aspect_params.spl'
for name in re.findall(r'^(?:pub )?(?:struct|enum) (\w+)',read(common),re.M):index[name]=[common]
for name in ['CompileMode','OutputFormat']:index[name]=[mode]
queue=['CompileOptions','NormalizedTargetProfileV1','TargetTraceCapabilityV1','FocusedNativeTargetProfileV1'];seen={}
for builtin in ['Result','Option','Dict','Array','Some','None','Ok','Err']:index.pop(builtin,None)
while queue:
 name=queue.pop()
 if name in seen:continue
 path=index[name][0];text=block(read(path),r'(?:pub )?(?:struct|enum|type|class) '+name+r'\b');seen[name]=(path,text)
 cleaned=re.sub(r'"""[\s\S]*?"""','',text);cleaned='\n'.join(x.split('#')[0] for x in cleaned.splitlines())
 queue.extend(x for x in re.findall(r'\b[A-Z][A-Za-z_0-9]*\b',cleaned) if x in index and x not in seen)
parts=[text for path,text in seen.values()]
for name in ['driver_core_compile_options_default','compileoptions_effective_mir_opt_level','compileoptions_normalize_mir_optimization','target_profile_normalize_v1','target_profile_identity_fields_v1','target_profile_identity_text_v1','compileoptions_target_profile_v1']:parts.append(decl(common,name))
parts += [decl(aspect,'AspectParamsV1','impl'), 'pub const ASPECT_CUTOVER_ATOMIC_EXT_V1 = "simple.instrumentation.cutover/atomic"\n',decl(args,'focused_native_build_target_profile_v1'),decl(xray,'driver_target_trace_capability_v1')]
(out/'production.spl').write_text('\n'.join(parts))
harness=(repo/'test/01_unit/compiler/driver/target_profile_native.spl').read_text();harness=re.sub(r'^use .*\n','',harness,flags=re.M)
(out/'src/main.spl').write_text('\n'.join(parts)+'\n'+harness)
prov='declarations |name, owner, sha256|\n'+''.join(f'    {name}, {path}, {hashlib.sha256(s.encode()).hexdigest()}\n' for name,(path,s) in sorted(seen.items()))
(out/'provenance.sdn').write_text(prov)
print(f'Actual records: {len(seen)}; production lines: {sum(len(p.splitlines()) for p in parts)}; fixture: {out}')

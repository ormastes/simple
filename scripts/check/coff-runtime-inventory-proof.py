"""Extract exact production inventory owners and replay retained runtime inputs."""
import hashlib, json, os, pathlib, re, subprocess, sys
root=pathlib.Path.cwd()
out=root/'build/coff-runtime-proof'
out.mkdir(parents=True)
source=root/'src/compiler_rust/compiler/src/pipeline/native_project/tools.rs'
text=source.read_text(encoding='utf-8')
def function(name):
    match=re.search(r'^(?:pub\([^\n]*?\) )?fn '+name+r'\(',text,re.M)
    assert match,name
    end=re.search(r'^}',text[match.start():],re.M)
    return text[match.start():match.start()+end.end()].replace('pub(super) ','')
names=['canonical_archive_symbol','archive_global_symbols','archive_weak_global_symbols_with_nm',
       'parse_archive_weak_global_symbols','coff_defined_weak_symbols','repair_coff_weak_fallback_indices',
       'bootstrap_mutex_runtime_requested_symbols','bootstrap_capsule_c_only_exports','bootstrap_capsule_symbol_ownership',
       'forbidden_archive_sections']
parts=[function(n) for n in names]
owner=root/'src/compiler_rust/compiler/src/pipeline/native_project/coff_weak_projection.rs'
selector=owner.with_name('coff_partial_link.rs')
prelude='use std::{path::{Path,PathBuf},collections::{BTreeMap,BTreeSet},process::Command};\n'
prelude+='#[path='+json.dumps(str(owner))+'] mod projection;\n#[path='+json.dumps(str(selector))+'] mod selector;\n'
# These adapters resolve genuine installed tools; symbol parsing/checks below
# are copied byte-for-byte from the production owner, never replaced by mocks.
prelude+='fn nm_command()->Result<Command,String>{Ok(Command::new(std::env::var("REAL_LLVM_NM").unwrap()))}\n'
prelude+='fn external_tool_path(p:&Path)->PathBuf{p.to_owned()}\n'
prelude+='fn find_objdump_tool()->Option<String>{std::env::var("REAL_LLVM_OBJDUMP").ok()}\n'
start=text.index('        let strong_external: Vec<&str> = localized_defined')
end=text.index('        let ar = find_archive_tool()?;',start)
gates=text[start:end]
main=r'''
fn checked(mut command: Command)->Result<(),String>{let o=command.output().map_err(|e|e.to_string())?; if !o.status.success(){return Err(String::from_utf8_lossy(&o.stderr).into());} Ok(())}
fn main()->Result<(),String>{
 let args:Vec<String>=std::env::args().collect();
 if args[1]=="private" {let path=Path::new(&args[2]); let names=BTreeSet::from(["dependency".to_string()]);projection::project(path,&names)?;projection::localize_weak(path,&names)?;return Ok(());}
 let core=Path::new(&args[1]); let native=Path::new(&args[2]); let work=Path::new(&args[3]);
 let (core_defined,_) = archive_global_symbols(core)?;
 let (native_defined,_) = archive_global_symbols(native)?;
 let mut roots=bootstrap_mutex_runtime_requested_symbols();
 for name in bootstrap_capsule_c_only_exports(&core_defined,&native_defined){if !roots.contains(&name){roots.push(name);}}
 let (roots,allowed)=bootstrap_capsule_symbol_ownership(&roots,&native_defined)?;
 let requested:BTreeSet<String>=roots.into_iter().collect();
 let allowed_external:BTreeSet<String>=allowed.into_iter().collect();
 for root in &requested {if core_defined.get(root)!=Some(&1){return Err(format!("root cardinality {root}"));}}
 let closure_object=work.join("closure.o"); let localized_object=work.join("localized.o");
 let mut ld=selector::command(true,"x86_64")?.ok_or("no BFD")?;
 for root in &requested{ld.arg(format!("--undefined={root}"));}
 ld.arg("--start-group").arg(core).arg("--end-group").arg("-o").arg(&closure_object);checked(ld)?;
 repair_coff_weak_fallback_indices(&closure_object)?;
 let (closure_defined,_) = archive_global_symbols(&closure_object)?;
 let localize_path=work.join("localize.syms"); let weaken_path=work.join("weaken.syms"); let coff_partial=true;
'''
ls=text.index('        let localize_text = closure_defined',text.index('fn project_stage4_archive_closure'))
le=text.index('        let objcopy = find_stage4_objcopy_tool',ls)
main+=text[ls:le]
main+=r'''
 let objcopy=selector::gnu_tool(&["x86_64-w64-mingw32-objcopy","objcopy"],"objcopy").ok_or("GNU objcopy")?;
 let mut cmd=Command::new(objcopy);cmd.arg(format!("--localize-symbols={}",localize_path.display()));
 for section in [".init_array",".init_array.*",".ctors",".ctors.*",".fini_array",".fini_array.*",".dtors",".dtors.*","__mod_init_func","__mod_term_func","__DATA,__mod_init_func","__DATA,__mod_term_func"]{cmd.arg(format!("--remove-section={section}"));}
 cmd.arg(&closure_object).arg(&localized_object);checked(cmd)?;
 projection::localize_weak(&localized_object,&localize_text.lines().map(str::to_owned).collect())?;
 projection::project(&localized_object,&weaken_text.lines().map(str::to_owned).collect())?;
 let (localized_defined,localized_undefined)=archive_global_symbols(&localized_object)?;
 let nm=selector::gnu_tool(&["x86_64-w64-mingw32-nm","nm"],"nm").ok_or("GNU nm")?;
 let mut localized_weak=archive_weak_global_symbols_with_nm(&localized_object,Some(&nm))?;
 localized_weak.extend(coff_defined_weak_symbols(&localized_object)?);
'''
main+=gates
main+='println!("requested={} allowed={} defined={} undefined={} weak={} inventory=PASS",requested.len(),allowed_external.len(),localized_defined.len(),localized_undefined.len(),localized_weak.len()); Ok(())}\n'
crate=out/'harness';(crate/'src').mkdir(parents=True)
(crate/'Cargo.toml').write_text('[package]\nname="coff-inventory-proof"\nversion="0.0.0"\nedition="2021"\n[dependencies]\nobject="=0.36.7"\n[workspace]\n',encoding='utf-8')
(crate/'src/main.rs').write_text(prelude+'\n'.join(parts)+main,encoding='utf-8')
fixture=pathlib.Path('retained-fixture')
inputs=[source,owner,selector,pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2]),fixture/'closure.o',fixture/'main.o']
manifest={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
(out/'inputs.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
env=dict(os.environ,CARGO_TARGET_DIR=str(out/'target'))
commands=[['cargo','build','--manifest-path',str(crate/'Cargo.toml'),'--jobs','1'],
          [str(out/'target/debug/coff-inventory-proof'),sys.argv[1],sys.argv[2],str(out)]]
for label,argv in zip(['build','inventory'],commands):
    result=subprocess.run(argv,env=env,capture_output=True,timeout=180)
    (out/(label+'.stdout')).write_bytes(result.stdout);(out/(label+'.stderr')).write_bytes(result.stderr)
    assert result.returncode==0,(label,result.returncode,result.stderr.decode(errors='replace'))
private=out/'private.o';private.write_bytes((fixture/'closure.o').read_bytes())
provider=out/'unrelated-owner.c';provider.write_text('int dependency(void) { return 99; }\n',encoding='utf-8')
commands=[['private-localize',[str(out/'target/debug/coff-inventory-proof'),'private',str(private)]]]
for label,extra in [('private-fallback',[]),('private-with-external-owner',[str(provider)])]:
    commands.append([label,[os.environ['REAL_CC'],'-fuse-ld=lld','--rtlib=compiler-rt','--unwindlib=libunwind',str(fixture/'main.o'),str(private),*extra,'-o',str(out/(label+'.exe'))]])
for label,argv in commands:
    result=subprocess.run(argv,capture_output=True,timeout=60)
    (out/(label+'.stdout')).write_bytes(result.stdout);(out/(label+'.stderr')).write_bytes(result.stderr)
    assert result.returncode==0,(label,result.returncode,result.stderr.decode(errors='replace'))
assert all(hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h for p,h in manifest.items())

"""Execute the actual non-Windows MinGW caller's archive selection, not a compiler build.

The standalone type adapter supplies target values only. Resolver, target flag,
symbol scanner and selection statements are copied verbatim from their owners.
The real import archives and actual nm/clang are exercised on a non-Windows host.
"""
import argparse, hashlib, json, pathlib, re, subprocess
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--cc',required=True); p.add_argument('--nm',required=True)
p.add_argument('--out',type=pathlib.Path,required=True)
a=p.parse_args(); a.out.mkdir(parents=True,exist_ok=False)
root=pathlib.Path(__file__).resolve().parents[2]
owner=root/'src/compiler_rust/compiler/src/pipeline/native_project'
linker=(owner/'linker.rs').read_text(); tools=(owner/'tools.rs').read_text(); stubs=(owner/'stubs.rs').read_text()
def function(source,name):
 start=source.index('fn '+name+'('); at=source.index('{',start); depth=1; end=at+1
 while depth:
  depth+=(source[end]=='{')-(source[end]=='}'); end+=1
 return source[start:end]
cross=linker.split('// MinGW (gnu) lane:')[1].split('#[cfg(not(target_os = "windows"))]')[1].split('#[cfg(target_os = "windows")]')[0]
start=cross.index('let system_libs = if '); end=cross.index('let stubs_o = ',start)
selection=cross[start:end]
assert 'imports, &system_libs,' in cross
assert '#[cfg(target_os = "windows")]\nfn gnu_link_line_libraries' not in linker
body='\n'.join(function(linker,n) for n in ['gnu_link_line_libraries','resolve_gnu_link_libraries'])
body+='\n'+function(stubs,'scan_defined_symbols')
body+='\n'+function(tools,'windows_gnu_target_flag')+'\n'+function(tools,'msvc_style_c_driver')
adapter=r'''
use std::path::PathBuf;
mod simple_common { pub mod target {
 #[derive(Clone,Copy,PartialEq)] pub enum TargetOS { Windows, Linux }
 #[derive(Clone,Copy)] pub enum TargetArch { Aarch64, Arm, X86, X86_64 }
 #[derive(Clone,Copy,PartialEq)] pub enum LinkerFlavor { Gnu, Msvc }
 #[derive(Clone,Copy)] pub struct Target {pub os:TargetOS,pub arch:TargetArch,pub flavor:LinkerFlavor}
 impl Target {pub fn linker_flavor(self)->LinkerFlavor {self.flavor}}
}}
use simple_common::target::{Target,TargetOS,TargetArch,LinkerFlavor};
fn external_tool_path(p:&PathBuf)->PathBuf {p.clone()}
fn nm_command()->Result<std::process::Command,String> {Ok(std::process::Command::new(std::env::var("PROOF_NM").unwrap()))}
'''
body+='\nfn actual_caller(cross_target:Target,is_msvc:bool,is_clang_cl:bool,cc:&str,cmd:&std::process::Command)->Vec<PathBuf>{\n'+selection+'\nsystem_libs\n}\n'
main=r'''
fn main() {
 let args:Vec<String>=std::env::args().collect();
 let mut cmd=std::process::Command::new(&args[1]); cmd.args(&args[2..]);
 let gnu=Target{os:TargetOS::Windows,arch:TargetArch::X86_64,flavor:LinkerFlavor::Gnu};
 let libraries=actual_caller(gnu,false,false,&args[1],&cmd);
 assert!(!libraries.is_empty(),"actual cross caller has no target archive authority");
 assert!(actual_caller(Target{os:TargetOS::Linux,..gnu},false,false,&args[1],&cmd).is_empty());
 assert!(actual_caller(Target{flavor:LinkerFlavor::Msvc,..gnu},true,false,&args[1],&cmd).is_empty());
 assert!(actual_caller(gnu,false,true,&args[1],&cmd).is_empty());
 let mut defined=std::collections::HashSet::new();
 scan_defined_symbols(&libraries,&["-g"],&mut defined).unwrap();
 for name in ["Thread32First","Thread32Next","PeekNamedPipe","ResumeThread","CreateToolhelp32Snapshot"] {assert!(defined.contains(name),"missing import {name}");}
 for lib in libraries {println!("L\t{}",lib.display());}
 let mut names:Vec<_>=defined.into_iter().collect(); names.sort();
 for name in names {println!("D\t{name}");}
}
'''
h=a.out/'caller'; (h/'src').mkdir(parents=True)
(h/'Cargo.toml').write_text('[package]\nname="cross-caller-proof"\nversion="0.1.0"\nedition="2021"\n[dependencies]\nrayon="1"\n')
(h/'src/main.rs').write_text(adapter+body+main)
config=(root/'src/compiler_rust/common/src/platform/link_config.rs').read_text()
libraries=re.findall(r'"([a-z0-9_]+)"',config.split('pub fn windows_mingw()')[1].split('libraries: vec![')[1].split(']')[0])
def run(argv,label):
 r=subprocess.run(list(map(str,argv)),capture_output=True,timeout=180,env={**__import__('os').environ,'PROOF_NM':a.nm})
 (a.out/(label+'.stdout')).write_bytes(r.stdout); (a.out/(label+'.stderr')).write_bytes(r.stderr)
 assert r.returncode==0,(label,r.returncode,r.stderr[-2000:])
 return r.stdout.decode()
run(['cargo','build','--quiet','--manifest-path',h/'Cargo.toml'],'build')
output=run([h/'target/debug/cross-caller-proof',a.cc,*['-l'+x for x in libraries]],'actual-caller')
defined=[line[2:] for line in output.splitlines() if line.startswith('D\t')]
archives=[line[2:] for line in output.splitlines() if line.startswith('L\t')]
(a.out/'authority.json').write_text(json.dumps({'defined':defined,'archives':{x:hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest() for x in archives},'selection':selection,'selection_sha256':hashlib.sha256(selection.encode()).hexdigest(),'owner_sha256':hashlib.sha256(linker.encode()).hexdigest(),'controls':'Windows GNU populated; Linux/MSVC/clang-cl empty','scope':'actual selection fragment/resolver/scanner; not rebuilt NativeProjectBuilder'},indent=2))
print('PASS actual cross-host selection and three exclusion controls')

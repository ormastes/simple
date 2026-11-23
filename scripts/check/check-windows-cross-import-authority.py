#!/usr/bin/env python3
"""Exercise the production import resolver/scanner without building a compiler.

Builds a tiny Rust harness from exact owner functions, then links a process
fixture against the retained native runtime. Execute its PE separately on Windows.
"""
import argparse
import hashlib
import json
import pathlib
import re
import shlex
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--cc', required=True)
p.add_argument('--nm', required=True)
p.add_argument('--gcc', required=True)
p.add_argument('--runtime', type=pathlib.Path, required=True)
p.add_argument('--out', type=pathlib.Path, required=True)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=False)
root = pathlib.Path(__file__).resolve().parents[2]
owner = root/'src/compiler_rust/compiler/src/pipeline/native_project'
linker = (owner/'linker.rs').read_text(encoding='utf-8')
stubs = (owner/'stubs.rs').read_text(encoding='utf-8')
config = (root/'src/compiler_rust/common/src/platform/link_config.rs').read_text(encoding='utf-8')

def function(source, name):
    start = source.index('fn '+name+'(')
    brace = source.index('{', start)
    depth = 1
    end = brace + 1
    while depth:
        depth += (source[end] == '{') - (source[end] == '}')
        end += 1
    return source[start:end]

def run(argv, label, timeout=180):
    r = subprocess.run(list(map(str, argv)), capture_output=True, timeout=timeout)
    (a.out/(label+'.stdout')).write_bytes(r.stdout)
    (a.out/(label+'.stderr')).write_bytes(r.stderr)
    assert r.returncode == 0, (label, r.returncode, r.stderr[-4000:])
    return r.stdout.decode()

# The regression includes the actual cross-host caller; merely compiling the
# previously host-gated resolver would not detect the original empty slice.
cross = linker.split('// MinGW (gnu) lane:')[1].split('#[cfg(not(target_os = "windows"))]')[1].split('#[cfg(target_os = "windows")]')[0]
assert 'gnu_link_line_libraries(' in cross and 'imports, &system_libs' in cross
assert '#[cfg(target_os = "windows")]\nfn gnu_link_line_libraries' not in linker
libs = re.findall(r'"([a-z0-9_]+)"', config.split('pub fn windows_mingw()')[1].split('libraries: vec![')[1].split(']')[0])
required = ['Thread32First', 'Thread32Next', 'PeekNamedPipe', 'K32GetPerformanceInfo', 'WriteFile', 'WriteFileEx', 'UnlockFileEx']
harness = a.out/'resolver'
(harness/'src').mkdir(parents=True)
(harness/'Cargo.toml').write_text('[package]\nname="import-authority-proof"\nversion="0.1.0"\nedition="2021"\n[dependencies]\nrayon="1"\n')
body = '\n'.join(function(linker, name) for name in ['gnu_link_line_libraries', 'resolve_gnu_link_libraries'])
body += '\n'+function(stubs, 'scan_defined_symbols')
prelude = 'use std::path::PathBuf;\nfn external_tool_path(p: &PathBuf) -> PathBuf {p.clone()}\nfn nm_command() -> Result<std::process::Command,String> {Ok(std::process::Command::new(std::env::var("PROOF_NM").unwrap()))}\n'
main = r'''
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut command = std::process::Command::new(&args[1]);
    command.args(&args[3..]);
    let target = if args[2] == "none" { None } else { Some(args[2].strip_prefix("expect-empty:").unwrap_or(args[2].as_str())) };
    let libs = gnu_link_line_libraries(&command, &args[1], target);
    if args[2].starts_with("expect-empty:") { assert!(libs.is_empty(), "failed driver stdout is not authority"); return; }
    assert!(!libs.is_empty());
    let mut defined = std::collections::HashSet::new();
    scan_defined_symbols(&libs, &["-g"], &mut defined).unwrap();
    for name in REQUIRED { assert!(defined.contains(*name), "missing genuine import {name}"); }
    assert!(!defined.contains("simple_intentional_bootstrap_shim_control"));
    for lib in libs { println!("{}", lib.display()); }
}
'''.replace('REQUIRED', '&'+json.dumps(required))
(harness/'src/main.rs').write_text(prelude+body+main)
import os
os.environ['PROOF_NM'] = a.nm
run(['cargo', 'build', '--manifest-path', harness/'Cargo.toml', '--quiet'], 'build-resolver')
exe = harness/'target/debug/import-authority-proof'
resolved = run([exe, a.cc, '--target=x86_64-w64-windows-gnu', *['-l'+lib for lib in libs]], 'actual-import-authority')
run([exe, a.gcc, 'none', '-lkernel32', '-lpsapi'], 'actual-gnu-import-authority')
rejected = a.out/'rejected-driver.sh'
rejected.write_text("printf '%s\\n' "+shlex.quote(resolved.splitlines()[0])+"\nexit 1\n")
run([exe, '/bin/sh', 'expect-empty:'+str(rejected)], 'failed-driver-is-not-authority')
run([exe, '/bin/sh', str(rejected), '-L'+str(pathlib.Path(resolved.splitlines()[0]).parent), '-lkernel32', '-lpsapi'], 'explicit-search-directory')
fixture = root/'scripts/check/fixtures/windows-bounded-process-provider.c'
run([a.cc, '--target=x86_64-w64-windows-gnu', '-fuse-ld=lld', '--rtlib=compiler-rt', '--unwindlib=libunwind', fixture, a.runtime, *['-l'+lib for lib in libs], '-o', a.out/'process-provider.exe'], 'process-provider-link')
imports = run([pathlib.Path(a.nm).with_name('llvm-readobj'), '--coff-imports', a.out/'process-provider.exe'], 'process-provider-imports')
for symbol in ['Thread32First', 'Thread32Next', 'ResumeThread', 'CreateToolhelp32Snapshot']:
    assert re.search(r'Symbol: '+symbol+r'\s*\(', imports), ('missing genuine PE import', symbol)
inputs = [owner/'linker.rs', owner/'stubs.rs', fixture, a.runtime]
(a.out/'inputs.json').write_text(json.dumps({str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in inputs}, indent=2))
(a.out/'result.json').write_text(json.dumps({'required_imports': required, 'negative_local_control': True, 'qualification': 'actual owner import discovery and retained-runtime PE link; Windows execution pending'}, indent=2))

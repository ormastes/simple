#!/usr/bin/env python3
"""Compile the actual receiver predicate with the actual TypeId contract."""
import argparse
from pathlib import Path
import subprocess
ap = argparse.ArgumentParser()
ap.add_argument('--output', required=True)
ap.add_argument('--rustc', default='rustc')
a=ap.parse_args()
root=Path(__file__).resolve().parents[2]
out=Path(a.output).resolve();out.mkdir(parents=True,exist_ok=True)
def region(text, signature):
    start=text.index(signature);end=text.index('{',start)+1;depth=1
    while depth:
        depth+=(text[end]=='{')-(text[end]=='}');end+=1
    return text[start:end]
types=(root/'src/compiler_rust/compiler/src/hir/types/type_system.rs').read_text()
actual_impl=region(types,'impl TypeId {')
calls=(root/'src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs').read_text()
predicate=region(calls,'pub(crate) fn byte_len_receiver_is_text_or_erased(')
prefix='pub mod hir { #[derive(Debug, Clone, Copy, PartialEq, Eq)] pub struct TypeId(pub u32);\n'+actual_impl+'\n}\n'
tests=r"""
#[test] fn builtin_and_custom_resolved_types_keep_their_identity() {
    for id in 0..=15 {
        let t=hir::TypeId(id);
        assert!(t.is_known());
        assert_eq!(byte_len_receiver_is_text_or_erased(Some(t)),t==hir::TypeId::STRING || t==hir::TypeId::ANY);
    }
    for id in [16,1024,u32::MAX-1] {
        let t=hir::TypeId(id);assert!(t.is_known());
        assert!(!byte_len_receiver_is_text_or_erased(Some(t)));
    }
}
#[test] fn legacy_erased_boundary_inputs_preserve_existing_admission() {
    assert!(byte_len_receiver_is_text_or_erased(None));
    let legacy=hir::TypeId(u32::MAX);
    assert!(!legacy.is_known());
    assert!(byte_len_receiver_is_text_or_erased(Some(legacy)));
}
"""
f=out/'receiver-typeid.rs';f.write_text(prefix+predicate+tests)
exe=out/'receiver-typeid.exe'
subprocess.run([a.rustc,'--edition=2021','--test','-Dwarnings',str(f),'-o',str(exe)],check=True)
subprocess.run([str(exe)],check=True)
negative=out/'receiver-typeid-negative.rs'
negative.write_text(prefix+predicate.replace('!t.is_known()','t == crate::hir::TypeId::UNKNOWN')+tests)
r=subprocess.run([a.rustc,'--edition=2021','--test','-Ddeprecated',str(negative),'-o',str(out/'negative.exe')],capture_output=True,text=True)
(out/'receiver-typeid-negative.log').write_text(r.stdout+r.stderr)
assert r.returncode != 0 and 'TypeId::UNKNOWN' in r.stderr, r.stderr
print('former TypeId constant deprecation negative control: PASS')

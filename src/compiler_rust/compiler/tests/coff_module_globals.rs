//! Windows module-global definitions must receive loader relocations under ASLR.

use object::{Object, ObjectSymbol};
use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::codegen::Codegen;
use simple_compiler::{hir, mir::lower_to_mir};
use simple_parser::Parser;

#[test]
fn coff_module_globals_have_relocatable_owner_definitions() {
    let source = "val RELOCATION_LABEL: text = \"module-global\"\n\
                  var RELOCATION_COUNTER: i64 = 40\n\
                  fn read_counter() -> i64:\n    RELOCATION_COUNTER\n";
    let ast = Parser::new(source).parse().expect("parse globals");
    let hir_module = hir::lower(&ast).expect("lower globals to HIR");
    let mir_module = lower_to_mir(&hir_module).expect("lower globals to MIR");

    for os in [TargetOS::Windows, TargetOS::Linux] {
        let bytes = Codegen::for_target(Target::new(TargetArch::X86_64, os))
            .expect("create target backend")
            .compile_module(&mir_module)
            .expect("emit module globals");
        let file = object::File::parse(bytes.as_slice()).expect("parse emitted object");
        for name in ["RELOCATION_LABEL", "RELOCATION_COUNTER"] {
            let symbol = file.symbol_by_name(name).expect("module global definition");
            assert!(symbol.section_index().is_some(), "{os:?}: {name} must own storage");
            assert_eq!(
                symbol.is_weak(),
                os != TargetOS::Windows,
                "{os:?}: {name} must use relocatable COFF owner linkage while preserving ELF preemption"
            );
        }
    }
}

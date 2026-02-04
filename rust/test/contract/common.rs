//! Common test utilities for MIR lowering tests

use simple_compiler::di::parse_di_config;
use simple_compiler::hir::{self, BinOp};
use simple_compiler::mir::{BlockId, ContractKind, ContractMode, MirInst, MirModule, Terminator};
use simple_compiler::mir::{lower_to_mir, lower_to_mir_with_mode, lower_to_mir_with_mode_and_di, MirLowerResult};
use simple_parser::Parser;
use toml::Value;

pub(crate) fn compile_to_mir(source: &str) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir(&hir_module)
}

pub(crate) fn compile_to_mir_with_di(source: &str, di_toml: &str) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let di_value: Value = di_toml.parse().expect("parse di toml");
    let di_config = parse_di_config(&di_value)
        .expect("di config parse")
        .expect("di config present");
    lower_to_mir_with_mode_and_di(&hir_module, ContractMode::All, Some(di_config))
}

pub(crate) fn compile_to_mir_with_mode(source: &str, mode: ContractMode) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir_with_mode(&hir_module, mode)
}

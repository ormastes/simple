//! Common test utilities for MIR lowering tests

use super::super::*;
use crate::di::parse_di_config;
use crate::hir::{self, BinOp};
use crate::mir::function::MirModule;
use crate::mir::{BlockId, ContractKind, MirInst, Terminator};
use simple_parser::Parser;

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
    let di_value: toml::Value = di_toml.parse().expect("parse di toml");
    let di_config = parse_di_config(&di_value)
        .expect("di config parse")
        .expect("di config present");
    lower_to_mir_with_mode_and_di(&hir_module, ContractMode::All, Some(di_config))
}

/// Like compile_to_mir but returns None instead of panicking on parse/HIR errors
pub(crate) fn try_compile_to_mir(source: &str) -> Option<MirLowerResult<MirModule>> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().ok()?;
    let hir_module = hir::lower(&ast).ok()?;
    Some(lower_to_mir(&hir_module))
}

pub(crate) fn compile_to_mir_with_mode(source: &str, mode: ContractMode) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir_with_mode(&hir_module, mode)
}

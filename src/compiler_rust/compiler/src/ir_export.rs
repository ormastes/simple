//! IR Export for LLM-Friendly Features (#885-887)
//!
//! Exports AST, HIR, and MIR to JSON format for tool consumption.

use serde::{Serialize, Serializer};
use serde_json;
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;

use crate::hir::HirModule;
use crate::mir::{MirInst, MirModule, Terminator, VReg};
use simple_parser::ast::Module as AstModule;

/// Export result for IR emission
pub type ExportResult = Result<(), String>;

/// Export AST to JSON
pub fn export_ast_json<W: Write>(module: &AstModule, writer: &mut W) -> ExportResult {
    // Create a serializable wrapper for AST
    let json = serde_json::to_string_pretty(&SerializableAst(module))
        .map_err(|e| format!("Failed to serialize AST: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write AST JSON: {}", e))
}

/// Export AST to file or stdout
pub fn export_ast(module: &AstModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file = File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_ast_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_ast_json(module, &mut handle)
        }
    }
}

/// Export HIR to JSON
pub fn export_hir_json<W: Write>(module: &HirModule, writer: &mut W) -> ExportResult {
    let json = serde_json::to_string_pretty(&SerializableHir(module))
        .map_err(|e| format!("Failed to serialize HIR: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write HIR JSON: {}", e))
}

/// Export HIR to file or stdout
pub fn export_hir(module: &HirModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file = File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_hir_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_hir_json(module, &mut handle)
        }
    }
}

/// Export MIR to JSON
pub fn export_mir_json<W: Write>(module: &MirModule, writer: &mut W) -> ExportResult {
    let json = serde_json::to_string_pretty(&SerializableMir(module))
        .map_err(|e| format!("Failed to serialize MIR: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write MIR JSON: {}", e))
}

/// Export MIR to file or stdout
pub fn export_mir(module: &MirModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file = File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_mir_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_mir_json(module, &mut handle)
        }
    }
}

// Serializable wrappers that implement custom JSON output

struct SerializableAst<'a>(&'a AstModule);

impl<'a> Serialize for SerializableAst<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("AstModule", 2)?;
        state.serialize_field("type", "AST")?;
        state.serialize_field("node_count", &self.0.items.len())?;
        state.end()
    }
}

struct SerializableHir<'a>(&'a HirModule);

impl<'a> Serialize for SerializableHir<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("HirModule", 3)?;
        state.serialize_field("type", "HIR")?;
        state.serialize_field("name", &self.0.name)?;
        state.serialize_field("function_count", &self.0.functions.len())?;
        state.end()
    }
}

struct SerializableMir<'a>(&'a MirModule);

impl<'a> Serialize for SerializableMir<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let functions: Vec<SerializableMirFunction<'_>> =
            self.0.functions.iter().map(SerializableMirFunction::from).collect();

        let mut state = serializer.serialize_struct("MirModule", 4)?;
        state.serialize_field("type", "MIR")?;
        state.serialize_field("name", &self.0.name)?;
        state.serialize_field("function_count", &self.0.functions.len())?;
        state.serialize_field("functions", &functions)?;
        state.end()
    }
}

#[derive(Serialize)]
struct SerializableMirFunction<'a> {
    name: &'a str,
    block_count: usize,
    blocks: Vec<SerializableMirBlock>,
}

impl<'a> From<&'a crate::mir::MirFunction> for SerializableMirFunction<'a> {
    fn from(func: &'a crate::mir::MirFunction) -> Self {
        SerializableMirFunction {
            name: &func.name,
            block_count: func.blocks.len(),
            blocks: func
                .blocks
                .iter()
                .map(|block| SerializableMirBlock {
                    id: block.id.0,
                    instruction_count: block.instructions.len(),
                    instructions: block
                        .instructions
                        .iter()
                        .map(SerializableMirInstruction::from)
                        .collect(),
                    terminator: SerializableMirTerminator::from(&block.terminator),
                })
                .collect(),
        }
    }
}

#[derive(Serialize)]
struct SerializableMirBlock {
    id: u32,
    instruction_count: usize,
    instructions: Vec<SerializableMirInstruction>,
    terminator: SerializableMirTerminator,
}

#[derive(Serialize)]
struct SerializableMirInstruction {
    kind: String,
    debug: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    dest: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    src: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    op: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    left: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    right: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    value_i64: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    value_bool: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    args: Vec<u32>,
}

impl From<&MirInst> for SerializableMirInstruction {
    fn from(inst: &MirInst) -> Self {
        let debug = format!("{inst:?}");
        let mut out = SerializableMirInstruction {
            kind: mir_inst_kind_from_debug(&debug),
            debug,
            dest: None,
            src: None,
            op: None,
            left: None,
            right: None,
            value_i64: None,
            value_bool: None,
            target: None,
            args: Vec::new(),
        };

        match inst {
            MirInst::ConstInt { dest, value } => {
                out.dest = Some(vreg_id(*dest));
                out.value_i64 = Some(*value);
            }
            MirInst::ConstBool { dest, value } => {
                out.dest = Some(vreg_id(*dest));
                out.value_bool = Some(*value);
            }
            MirInst::Copy { dest, src } => {
                out.dest = Some(vreg_id(*dest));
                out.src = Some(vreg_id(*src));
            }
            MirInst::BinOp { dest, op, left, right } => {
                out.dest = Some(vreg_id(*dest));
                out.op = Some(format!("{op:?}"));
                out.left = Some(vreg_id(*left));
                out.right = Some(vreg_id(*right));
            }
            MirInst::UnaryOp { dest, op, operand } => {
                out.dest = Some(vreg_id(*dest));
                out.op = Some(format!("{op:?}"));
                out.src = Some(vreg_id(*operand));
            }
            MirInst::Cast {
                dest,
                source,
                from_ty,
                to_ty,
            } => {
                out.dest = Some(vreg_id(*dest));
                out.src = Some(vreg_id(*source));
                out.op = Some(format!("{from_ty:?}->{to_ty:?}"));
            }
            MirInst::Call { dest, target, args } => {
                out.dest = dest.map(vreg_id);
                out.target = Some(format!("{target:?}"));
                out.args = args.iter().copied().map(vreg_id).collect();
            }
            _ => {}
        }

        out
    }
}

#[derive(Serialize)]
struct SerializableMirTerminator {
    kind: &'static str,
    debug: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    value: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    cond: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    then_block: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    else_block: Option<u32>,
}

impl From<&Terminator> for SerializableMirTerminator {
    fn from(term: &Terminator) -> Self {
        let mut out = SerializableMirTerminator {
            kind: mir_terminator_kind(term),
            debug: format!("{term:?}"),
            value: None,
            target: None,
            cond: None,
            then_block: None,
            else_block: None,
        };

        match term {
            Terminator::Return(value) => {
                out.value = value.map(vreg_id);
            }
            Terminator::Jump(target) => {
                out.target = Some(target.0);
            }
            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                out.cond = Some(vreg_id(*cond));
                out.then_block = Some(then_block.0);
                out.else_block = Some(else_block.0);
            }
            Terminator::Unreachable => {}
        }

        out
    }
}

fn vreg_id(reg: VReg) -> u32 {
    reg.0
}

fn mir_terminator_kind(term: &Terminator) -> &'static str {
    match term {
        Terminator::Return(_) => "Return",
        Terminator::Jump(_) => "Jump",
        Terminator::Branch { .. } => "Branch",
        Terminator::Unreachable => "Unreachable",
    }
}

fn mir_inst_kind_from_debug(debug: &str) -> String {
    let kind: String = debug
        .chars()
        .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
        .collect();
    if kind.is_empty() {
        "Unknown".to_string()
    } else {
        kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_export_ast_json_simple() {
        use simple_parser::Parser;

        let source = "fn main():\n    return 42";
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse failed");

        let mut output = Vec::new();
        let result = export_ast_json(&module, &mut output);
        assert!(result.is_ok());

        let json = String::from_utf8(output).unwrap();
        // Check for "type" field with "AST" value (allow for spacing variations in JSON)
        assert!(
            json.contains("\"type\"") && json.contains("\"AST\""),
            "Expected JSON to contain type field with AST value, got: {}",
            json
        );
    }

    #[test]
    fn test_export_hir_json() {
        // HIR requires a full compilation context
        // This is a placeholder for when HIR is more stable
        // For now, just test that the function exists
    }

    #[test]
    fn test_export_mir_json() {
        use crate::hir::{BinOp, TypeId};
        use crate::mir::{BlockId, MirFunction, MirInst, MirModule, Terminator, VReg};
        use simple_parser::ast::Visibility;

        let mut module = MirModule::new();
        module.name = Some("mir_export_test".to_string());

        let mut func = MirFunction::new("bitfield_like".to_string(), TypeId::I64, Visibility::Private);
        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 4,
        });
        entry.instructions.push(MirInst::BinOp {
            dest: VReg(1),
            op: BinOp::ShiftRight,
            left: VReg(2),
            right: VReg(0),
        });
        entry.terminator = Terminator::Return(Some(VReg(1)));
        module.functions.push(func);

        let mut output = Vec::new();
        export_mir_json(&module, &mut output).expect("MIR export should succeed");
        let json = String::from_utf8(output).unwrap();
        let value: serde_json::Value = serde_json::from_str(&json).expect("MIR JSON should parse");
        let instructions = value["functions"][0]["blocks"][0]["instructions"]
            .as_array()
            .expect("instructions should be exported as structured JSON objects");

        assert!(json.contains("\"functions\""), "missing functions payload: {json}");
        assert!(json.contains("bitfield_like"), "missing function name: {json}");
        assert_eq!(instructions[0]["kind"], "ConstInt");
        assert_eq!(instructions[0]["dest"], 0);
        assert_eq!(instructions[0]["value_i64"], 4);
        assert_eq!(instructions[1]["kind"], "BinOp");
        assert_eq!(instructions[1]["dest"], 1);
        assert_eq!(instructions[1]["op"], "ShiftRight");
        assert_eq!(instructions[1]["left"], 2);
        assert_eq!(instructions[1]["right"], 0);
        assert_eq!(value["functions"][0]["blocks"][0]["terminator"]["kind"], "Return");
        assert_eq!(value["functions"][0]["blocks"][0]["terminator"]["value"], 1);
    }
}

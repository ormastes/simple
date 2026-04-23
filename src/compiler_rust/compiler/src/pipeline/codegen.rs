//! Code generation, JIT compilation, and object file emission.

use simple_common::target::Target;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::env;
use std::path::Path;

use super::core::CompilerPipeline;
use crate::codegen::llvm::LlvmBackend;
use crate::codegen::{backend_trait::NativeBackend, BackendKind, Codegen};
use crate::hir::{BinOp, HirType, TypeRegistry, UnaryOp};
use crate::import_loader::load_module_with_imports;
use crate::mir;
use crate::mir::{CallTarget, MirFunction, MirInst, GpuMemoryScope, Terminator};
use crate::monomorphize::monomorphize_module;
use crate::CompileError;

impl CompilerPipeline {
    pub(super) fn compile_mir_to_object(
        &self,
        mir_module: &mir::MirModule,
        target: Target,
    ) -> Result<Vec<u8>, CompileError> {
        if target.arch.is_32bit() && cfg!(not(feature = "llvm")) {
            return Err(CompileError::Codegen(
                "32-bit targets require the LLVM backend; build with --features llvm".to_string(),
            ));
        }

        // Coverage module is complete and available via SIMPLE_COVERAGE env var
        let coverage_enabled = crate::coverage::is_coverage_enabled();
        let backend = select_backend(&target)?;

        match backend {
            BackendKind::Cranelift => {
                let mut codegen = Codegen::for_target(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                // During bootstrap, emit the entry module without mangling so the linker
                // sees a public main symbol.
                codegen.set_entry_module(true);
                codegen.set_module_prefix(String::new());
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            BackendKind::Llvm => {
                let backend = LlvmBackend::new(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend
                    .with_coverage(coverage_enabled)
                    .compile(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            #[cfg(feature = "vulkan")]
            BackendKind::Vulkan => {
                use crate::codegen::vulkan::VulkanBackend;
                let mut backend = VulkanBackend::new(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend.compile(mir_module)
            }
            BackendKind::Software => {
                // Software backend is for GPU kernel fallback, not general compilation
                Err(CompileError::Codegen(
                    "Software GPU backend cannot be used for general compilation; use for_gpu_kernel() instead"
                        .to_string(),
                ))
            }
            BackendKind::CraneliftJit | BackendKind::LlvmJit | BackendKind::AutoJit => {
                // JIT backends are for in-process execution, not AOT compilation.
                // Fall back to Cranelift AOT for object code generation.
                let codegen = Codegen::for_target(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
        }
    }

    /// Compile a source file to PTX (NVIDIA GPU assembly).
    ///
    /// Loads the source with imports, parses, type-checks, lowers to MIR,
    /// then emits PTX text for all functions (kernel functions get `.entry` directives).
    pub fn compile_file_to_ptx(&mut self, source: &Path, output: &Path) -> Result<(), CompileError> {
        // Load module with import resolution
        let ast_module = load_module_with_imports(source, &mut HashSet::new())?;

        // Monomorphize generics
        let ast_module = monomorphize_module(&ast_module);

        // Type check and lower to MIR (with module resolution for imports)
        let mir_module = self.type_check_and_lower_with_context(&ast_module, source)?;

        // Generate PTX from MIR
        let ptx = generate_ptx(&mir_module);

        // Write PTX to output file
        std::fs::write(output, ptx).map_err(|e| CompileError::Io(format!("{e}")))?;
        Ok(())
    }

    /// Compile a source file to VHDL-2008 for the supported combinational subset.
    ///
    /// This is intentionally conservative: unsupported MIR instructions fail
    /// instead of being silently dropped.
    pub fn compile_file_to_vhdl(&mut self, source: &Path, output: &Path) -> Result<(), CompileError> {
        let ast_module = load_module_with_imports(source, &mut HashSet::new())?;
        let ast_module = monomorphize_module(&ast_module);
        let mir_module = self.type_check_and_lower_with_context(&ast_module, source)?;
        let vhdl = generate_vhdl(&mir_module)?;
        std::fs::write(output, vhdl).map_err(|e| CompileError::Io(format!("{e}")))?;
        Ok(())
    }
}

// =============================================================================
// VHDL code generation from MIR
// =============================================================================

fn generate_vhdl(module: &mir::MirModule) -> Result<String, CompileError> {
    let types = &module.type_registry;
    let entity_table = vhdl_entity_table(module)?;
    let mut out = String::new();
    for func in &module.functions {
        if !entity_table.contains_key(func.name.as_str()) {
            continue;
        }
        if !out.is_empty() {
            out.push_str("\n\n");
        }
        emit_vhdl_function(&mut out, func, types, &entity_table)?;
    }
    if out.trim().is_empty() {
        return Err(CompileError::Codegen(
            "VHDL backend found no hardware functions to emit".to_string(),
        ));
    }
    Ok(out)
}

fn vhdl_entity_table<'a>(module: &'a mir::MirModule) -> Result<BTreeMap<&'a str, &'a MirFunction>, CompileError> {
    let mut entities = BTreeMap::new();
    let mut sanitized_names: HashMap<String, String> = HashMap::new();
    for func in &module.functions {
        if !is_vhdl_entity_function(func) {
            continue;
        }
        let sanitized = sanitize_vhdl_ident(&func.name);
        if let Some(previous) = sanitized_names.insert(sanitized.clone(), func.name.clone()) {
            return Err(CompileError::Codegen(format!(
                "VHDL entity identifier collision after sanitization: functions `{}` and `{}` both map to `{}`",
                previous, func.name, sanitized
            )));
        }
        entities.insert(func.name.as_str(), func);
    }
    Ok(entities)
}

fn is_vhdl_entity_function(func: &MirFunction) -> bool {
    func.attributes.iter().any(|attr| attr == "hardware")
}

fn emit_vhdl_function(
    out: &mut String,
    func: &MirFunction,
    types: &TypeRegistry,
    entity_table: &BTreeMap<&str, &MirFunction>,
) -> Result<(), CompileError> {
    let entity = sanitize_vhdl_ident(&func.name);
    let mut state = VhdlLowerState::default();
    let mut return_assignments: Option<Vec<String>> = None;
    let return_abi = vhdl_return_abi(func, types)?;
    let mut ports = Vec::new();
    for param in &func.params {
        ports.push(VhdlPort::input(
            sanitize_vhdl_ident(&param.name),
            param.name.clone(),
            param.ty,
        ));
    }
    ports.extend(return_abi.ports().iter().cloned());
    validate_vhdl_port_names(&entity, &func.name, &ports)?;

    out.push_str("library ieee;\n");
    out.push_str("use ieee.std_logic_1164.all;\n");
    out.push_str("use ieee.numeric_std.all;\n\n");
    out.push_str(&format!("entity {} is\n", entity));
    out.push_str("    port (\n");
    for (idx, port) in ports.iter().enumerate() {
        let semicolon = if idx + 1 == ports.len() { "" } else { ";" };
        out.push_str(&format!(
            "        {} : {} {}{}\n",
            port.name,
            port.direction.as_vhdl(),
            vhdl_type(port.ty, types)?,
            semicolon
        ));
    }
    out.push_str("    );\n");
    out.push_str(&format!("end entity {};\n\n", entity));
    out.push_str(&format!("architecture rtl of {} is\n", entity));

    if let Some(entry) = func.blocks.first() {
        if let Terminator::Branch {
            cond,
            then_block,
            else_block,
        } = &entry.terminator
        {
            lower_vhdl_block_instructions(func, &mut state, entry, types, entity_table)?;
            let cond_expr = reg_expr_for_type(
                &state.reg_expr,
                &state.reg_int_const,
                *cond,
                crate::hir::TypeId::BOOL,
                types,
            )?;
            let base_assign_len = state.assigns.len();
            let mut then_state = state.clone();
            let mut else_state = state.clone();
            let then_exprs =
                lower_vhdl_return_block(func, &mut then_state, *then_block, &return_abi, types, entity_table)?;
            let else_exprs =
                lower_vhdl_return_block(func, &mut else_state, *else_block, &return_abi, types, entity_table)?;
            let then_assigns = then_state.assigns.split_off(base_assign_len);
            let else_assigns = else_state.assigns.split_off(base_assign_len);
            state.signals.extend(then_state.signals);
            state.signals.extend(else_state.signals);
            state.instances.extend(then_state.instances);
            state.instances.extend(else_state.instances);
            state.assigns.extend(then_assigns);
            state.assigns.extend(else_assigns);
            return_assignments = Some(branch_return_assignments(func, then_exprs, else_exprs, &cond_expr)?);
        }
    }

    if return_assignments.is_none() {
        for block in &func.blocks {
            lower_vhdl_block_instructions(func, &mut state, block, types, entity_table)?;
            match &block.terminator {
                Terminator::Return(Some(reg)) => {
                    let exprs = return_output_exprs(func, &state, &return_abi, *reg, types)?;
                    return_assignments = Some(push_return_assignments(exprs));
                }
                Terminator::Return(None) => {}
                Terminator::Unreachable if block.instructions.is_empty() => {}
                other => {
                    return Err(CompileError::Codegen(format!(
                        "VHDL backend unsupported terminator in {}: {:?}",
                        func.name, other
                    )));
                }
            }
        }
    }

    for (name, ty) in &state.signals {
        out.push_str(&format!("    signal {} : {};\n", name, vhdl_type(*ty, types)?));
    }
    out.push_str("begin\n");
    for instance in state.instances {
        out.push_str(&instance);
        out.push('\n');
    }
    for assign in state.assigns {
        out.push_str(&assign);
        out.push('\n');
    }
    if let Some(assignments) = return_assignments {
        for assign in assignments {
            out.push_str(&assign);
            out.push('\n');
        }
    }
    out.push_str("end architecture rtl;\n");
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VhdlPortDirection {
    In,
    Out,
}

impl VhdlPortDirection {
    fn as_vhdl(&self) -> &'static str {
        match self {
            Self::In => "in",
            Self::Out => "out",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VhdlPort {
    name: String,
    source_name: String,
    direction: VhdlPortDirection,
    ty: crate::hir::TypeId,
}

impl VhdlPort {
    fn input(name: String, source_name: String, ty: crate::hir::TypeId) -> Self {
        Self {
            name,
            source_name,
            direction: VhdlPortDirection::In,
            ty,
        }
    }

    fn output(name: String, source_name: String, ty: crate::hir::TypeId) -> Self {
        Self {
            name,
            source_name,
            direction: VhdlPortDirection::Out,
            ty,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VhdlReturnField {
    port_name: String,
    source_name: String,
    ty: crate::hir::TypeId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VhdlReturnAbi {
    Scalar(VhdlReturnField),
    AnonymousTuple(Vec<VhdlReturnField>),
    LabeledTuple(Vec<VhdlReturnField>),
}

impl VhdlReturnAbi {
    fn ports(&self) -> Vec<VhdlPort> {
        self.fields()
            .iter()
            .map(|field| VhdlPort::output(field.port_name.clone(), field.source_name.clone(), field.ty))
            .collect()
    }

    fn fields(&self) -> &[VhdlReturnField] {
        match self {
            Self::Scalar(fields) => std::slice::from_ref(fields),
            Self::AnonymousTuple(fields) | Self::LabeledTuple(fields) => fields,
        }
    }
}

fn vhdl_return_abi(func: &MirFunction, types: &TypeRegistry) -> Result<VhdlReturnAbi, CompileError> {
    match types.get(func.return_type) {
        Some(HirType::Tuple(fields)) if fields.is_empty() => Err(CompileError::Codegen(format!(
            "VHDL backend unsupported empty tuple return in {}",
            func.name
        ))),
        Some(HirType::Tuple(fields)) => Ok(VhdlReturnAbi::AnonymousTuple(
            fields
                .iter()
                .enumerate()
                .map(|(index, ty)| VhdlReturnField {
                    port_name: format!("out{}", index),
                    source_name: format!("out{}", index),
                    ty: *ty,
                })
                .collect(),
        )),
        Some(HirType::LabeledTuple(fields)) if fields.is_empty() => Err(CompileError::Codegen(format!(
            "VHDL backend unsupported empty labeled tuple return in {}",
            func.name
        ))),
        Some(HirType::LabeledTuple(fields)) => Ok(VhdlReturnAbi::LabeledTuple(
            fields
                .iter()
                .map(|(label, ty)| VhdlReturnField {
                    port_name: sanitize_vhdl_ident(label),
                    source_name: label.clone(),
                    ty: *ty,
                })
                .collect(),
        )),
        _ => Ok(VhdlReturnAbi::Scalar(VhdlReturnField {
            port_name: "result_out".to_string(),
            source_name: "result_out".to_string(),
            ty: func.return_type,
        })),
    }
}

fn validate_vhdl_port_names(entity: &str, source_entity: &str, ports: &[VhdlPort]) -> Result<(), CompileError> {
    let mut seen: HashMap<String, String> = HashMap::new();
    seen.insert(entity.to_string(), format!("entity `{}`", source_entity));
    for port in ports {
        if let Some(previous) = seen.insert(port.name.clone(), format!("port `{}`", port.source_name)) {
            return Err(CompileError::Codegen(format!(
                "VHDL identifier collision after sanitization: {} and port `{}` both map to `{}`",
                previous, port.source_name, port.name
            )));
        }
    }
    Ok(())
}

#[derive(Clone, Default)]
struct VhdlLowerState {
    reg_expr: HashMap<u32, String>,
    reg_ty: HashMap<u32, crate::hir::TypeId>,
    reg_tuple_fields: HashMap<u32, Vec<VhdlTupleFieldExpr>>,
    reg_int_const: HashMap<u32, i64>,
    addr_local: HashMap<u32, usize>,
    local_expr: HashMap<usize, String>,
    local_ty: HashMap<usize, crate::hir::TypeId>,
    local_tuple_fields: HashMap<usize, Vec<VhdlTupleFieldExpr>>,
    signals: BTreeSet<(String, crate::hir::TypeId)>,
    instances: Vec<String>,
    call_ordinal: usize,
    assigns: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VhdlTupleFieldExpr {
    index: usize,
    ty: crate::hir::TypeId,
    expr: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VhdlReturnOutputExpr {
    port_name: String,
    expr: String,
}

fn lower_vhdl_block_instructions(
    func: &MirFunction,
    state: &mut VhdlLowerState,
    block: &crate::mir::MirBlock,
    types: &TypeRegistry,
    entity_table: &BTreeMap<&str, &MirFunction>,
) -> Result<(), CompileError> {
    for inst in &block.instructions {
        lower_vhdl_instruction(func, state, inst, types, entity_table)?;
    }
    Ok(())
}

fn lower_vhdl_return_block(
    func: &MirFunction,
    state: &mut VhdlLowerState,
    id: crate::mir::BlockId,
    return_abi: &VhdlReturnAbi,
    types: &TypeRegistry,
    entity_table: &BTreeMap<&str, &MirFunction>,
) -> Result<Vec<VhdlReturnOutputExpr>, CompileError> {
    let block = func
        .blocks
        .iter()
        .find(|block| block.id == id)
        .ok_or_else(|| CompileError::Codegen(format!("VHDL backend missing block {:?}", id)))?;
    lower_vhdl_block_instructions(func, state, block, types, entity_table)?;
    match &block.terminator {
        Terminator::Return(Some(reg)) => return_output_exprs(func, state, return_abi, *reg, types),
        other => Err(CompileError::Codegen(format!(
            "VHDL backend only supports if/else branches whose arms return in {}: {:?}",
            func.name, other
        ))),
    }
}

fn return_output_exprs(
    func: &MirFunction,
    state: &VhdlLowerState,
    return_abi: &VhdlReturnAbi,
    reg: mir::VReg,
    types: &TypeRegistry,
) -> Result<Vec<VhdlReturnOutputExpr>, CompileError> {
    match return_abi {
        VhdlReturnAbi::Scalar(field) => Ok(vec![VhdlReturnOutputExpr {
            port_name: field.port_name.clone(),
            expr: reg_expr_for_type(&state.reg_expr, &state.reg_int_const, reg, field.ty, types)?,
        }]),
        VhdlReturnAbi::AnonymousTuple(fields) | VhdlReturnAbi::LabeledTuple(fields) => {
            let tuple_fields = state.reg_tuple_fields.get(&reg.0).ok_or_else(|| {
                CompileError::Codegen(format!(
                    "VHDL backend expected tuple return value in {}, but v{} is not a virtual tuple",
                    func.name, reg.0
                ))
            })?;
            if tuple_fields.len() != fields.len() {
                return Err(CompileError::Codegen(format!(
                    "VHDL backend tuple return arity mismatch in {}: ABI has {} fields, v{} has {}",
                    func.name,
                    fields.len(),
                    reg.0,
                    tuple_fields.len()
                )));
            }
            fields
                .iter()
                .zip(tuple_fields.iter())
                .enumerate()
                .map(|(index, (field, tuple_field))| {
                    if tuple_field.index != index {
                        return Err(CompileError::Codegen(format!(
                            "VHDL backend tuple return field order mismatch in {} at field {}",
                            func.name, index
                        )));
                    }
                    if tuple_field.ty != field.ty {
                        return Err(CompileError::Codegen(format!(
                            "VHDL backend tuple return type mismatch in {}.{}",
                            func.name, field.source_name
                        )));
                    }
                    Ok(VhdlReturnOutputExpr {
                        port_name: field.port_name.clone(),
                        expr: tuple_field.expr.clone(),
                    })
                })
                .collect()
        }
    }
}

fn push_return_assignments(exprs: Vec<VhdlReturnOutputExpr>) -> Vec<String> {
    exprs
        .into_iter()
        .map(|expr| format!("    {} <= {};", expr.port_name, expr.expr))
        .collect()
}

fn branch_return_assignments(
    func: &MirFunction,
    then_exprs: Vec<VhdlReturnOutputExpr>,
    else_exprs: Vec<VhdlReturnOutputExpr>,
    cond_expr: &str,
) -> Result<Vec<String>, CompileError> {
    if then_exprs.len() != else_exprs.len() {
        return Err(CompileError::Codegen(format!(
            "VHDL backend branch return arity mismatch in {}: then has {}, else has {}",
            func.name,
            then_exprs.len(),
            else_exprs.len()
        )));
    }
    then_exprs
        .into_iter()
        .zip(else_exprs)
        .map(|(then_expr, else_expr)| {
            if then_expr.port_name != else_expr.port_name {
                return Err(CompileError::Codegen(format!(
                    "VHDL backend branch return port mismatch in {}: then {}, else {}",
                    func.name, then_expr.port_name, else_expr.port_name
                )));
            }
            Ok(format!(
                "    {} <= {} when {} = '1' else {};",
                then_expr.port_name, then_expr.expr, cond_expr, else_expr.expr
            ))
        })
        .collect()
}

fn lower_vhdl_instruction(
    func: &MirFunction,
    state: &mut VhdlLowerState,
    inst: &MirInst,
    types: &TypeRegistry,
    entity_table: &BTreeMap<&str, &MirFunction>,
) -> Result<(), CompileError> {
    match inst {
        MirInst::LocalAddr { dest, local_index } => {
            state.addr_local.insert(dest.0, *local_index);
        }
        MirInst::Load { dest, addr, ty } => {
            let local_index = state.addr_local.get(&addr.0).ok_or_else(|| {
                CompileError::Codegen(format!("VHDL unsupported load from non-local address v{}", addr.0))
            })?;
            if let Some(fields) = state.local_tuple_fields.get(local_index).cloned() {
                state.reg_tuple_fields.insert(dest.0, fields);
                state.reg_ty.insert(dest.0, *ty);
                return Ok(());
            }
            if let Some(expr) = state.local_expr.get(local_index).cloned() {
                state.reg_expr.insert(dest.0, expr);
                state
                    .reg_ty
                    .insert(dest.0, state.local_ty.get(local_index).copied().unwrap_or(*ty));
                return Ok(());
            }
            let name = local_name(func, *local_index)?;
            state.reg_expr.insert(dest.0, sanitize_vhdl_ident(name));
            state.reg_ty.insert(dest.0, *ty);
        }
        MirInst::ConstInt { dest, value } => {
            state.reg_int_const.insert(dest.0, *value);
            state.reg_expr.insert(dest.0, value.to_string());
        }
        MirInst::ConstBool { dest, value } => {
            state
                .reg_expr
                .insert(dest.0, if *value { "'1'".to_string() } else { "'0'".to_string() });
            state.reg_ty.insert(dest.0, crate::hir::TypeId::BOOL);
        }
        MirInst::Copy { dest, src } => {
            if let Some(expr) = state.reg_expr.get(&src.0).cloned() {
                state.reg_expr.insert(dest.0, expr);
            } else if !state.reg_tuple_fields.contains_key(&src.0) {
                return Err(CompileError::Codegen(format!(
                    "VHDL backend has no expression for copy source v{} in {}",
                    src.0, func.name
                )));
            }
            if let Some(fields) = state.reg_tuple_fields.get(&src.0).cloned() {
                state.reg_tuple_fields.insert(dest.0, fields);
            }
            if let Some(value) = state.reg_int_const.get(&src.0).copied() {
                state.reg_int_const.insert(dest.0, value);
            }
            if let Some(ty) = state.reg_ty.get(&src.0).copied() {
                state.reg_ty.insert(dest.0, ty);
            }
        }
        MirInst::BinOp { dest, op, left, right } => {
            let left_ty = state
                .reg_ty
                .get(&left.0)
                .copied()
                .or_else(|| state.reg_ty.get(&right.0).copied())
                .unwrap_or(func.return_type);
            let right_ty = state
                .reg_ty
                .get(&right.0)
                .copied()
                .or_else(|| state.reg_ty.get(&left.0).copied())
                .unwrap_or(func.return_type);
            let left_expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *left, left_ty, types)?;
            let right_expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *right, right_ty, types)?;
            let expr = vhdl_binop(op, &left_expr, &right_expr)?;
            let ty = binop_result_type(*op, left_ty);
            let sig = format!("tmp_{}", dest.0);
            state.signals.insert((sig.clone(), ty));
            state.assigns.push(format!("    {} <= {};", sig, expr));
            state.reg_expr.insert(dest.0, sig);
            state.reg_ty.insert(dest.0, ty);
        }
        MirInst::UnaryOp { dest, op, operand } => {
            let operand_ty = state.reg_ty.get(&operand.0).copied().unwrap_or(func.return_type);
            let operand_expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *operand, operand_ty, types)?;
            let expr = vhdl_unaryop(op, &operand_expr)?;
            let sig = format!("tmp_{}", dest.0);
            state.signals.insert((sig.clone(), operand_ty));
            state.assigns.push(format!("    {} <= {};", sig, expr));
            state.reg_expr.insert(dest.0, sig);
            state.reg_ty.insert(dest.0, operand_ty);
        }
        MirInst::BoxInt { dest, value } => {
            let ty = state.reg_ty.get(&value.0).copied().unwrap_or(crate::hir::TypeId::I64);
            let expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *value, ty, types)?;
            state.reg_expr.insert(dest.0, expr);
            state.reg_ty.insert(dest.0, ty);
            if let Some(value) = state.reg_int_const.get(&value.0).copied() {
                state.reg_int_const.insert(dest.0, value);
            }
        }
        MirInst::TupleLit { dest, elements } => {
            let mut fields = Vec::with_capacity(elements.len());
            for (index, element) in elements.iter().enumerate() {
                let ty = state.reg_ty.get(&element.0).copied().ok_or_else(|| {
                    CompileError::Codegen(format!(
                        "VHDL backend cannot infer tuple field {} type for v{} in {}",
                        index, element.0, func.name
                    ))
                })?;
                fields.push(VhdlTupleFieldExpr {
                    index,
                    ty,
                    expr: reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *element, ty, types)?,
                });
            }
            state.reg_tuple_fields.insert(dest.0, fields);
            state.reg_ty.insert(dest.0, func.return_type);
        }
        MirInst::Store { addr, value, ty } => {
            let local_index = state.addr_local.get(&addr.0).copied().ok_or_else(|| {
                CompileError::Codegen(format!("VHDL unsupported store to non-local address v{}", addr.0))
            })?;
            state.local_ty.insert(local_index, *ty);
            if let Some(fields) = state.reg_tuple_fields.get(&value.0).cloned() {
                state.local_tuple_fields.insert(local_index, fields);
                state.local_expr.remove(&local_index);
            } else {
                let expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *value, *ty, types)?;
                state.local_expr.insert(local_index, expr);
                state.local_tuple_fields.remove(&local_index);
            }
        }
        MirInst::Call { dest, target, args } => {
            if target.name() == "rt_value_bool" {
                lower_vhdl_value_bool(func, state, *dest, args)?;
                return Ok(());
            }
            if target.name() == "rt_tuple_get" {
                lower_vhdl_tuple_get(func, state, *dest, args)?;
                return Ok(());
            }
            lower_vhdl_call(func, state, *dest, target, args, types, entity_table)?;
        }
        MirInst::Drop { .. } => {}
        other => {
            return Err(CompileError::Codegen(format!(
                "VHDL backend unsupported MIR instruction in {}: {:?}",
                func.name, other
            )))
        }
    }
    Ok(())
}

fn lower_vhdl_value_bool(
    func: &MirFunction,
    state: &mut VhdlLowerState,
    dest: Option<mir::VReg>,
    args: &[mir::VReg],
) -> Result<(), CompileError> {
    let dest = dest.ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported void bool boxing call in {}",
            func.name
        ))
    })?;
    if args.len() != 1 {
        return Err(CompileError::Codegen(format!(
            "VHDL backend bool boxing call in {} expects 1 argument, got {}",
            func.name,
            args.len()
        )));
    }
    let arg = args[0];
    let expr = reg_expr_for(&state.reg_expr, arg)?;
    state.reg_expr.insert(dest.0, expr);
    state.reg_ty.insert(dest.0, crate::hir::TypeId::BOOL);
    Ok(())
}

fn lower_vhdl_tuple_get(
    func: &MirFunction,
    state: &mut VhdlLowerState,
    dest: Option<mir::VReg>,
    args: &[mir::VReg],
) -> Result<(), CompileError> {
    let dest = dest.ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported void tuple projection in {}",
            func.name
        ))
    })?;
    if args.len() != 2 {
        return Err(CompileError::Codegen(format!(
            "VHDL backend tuple projection in {} expects 2 arguments, got {}",
            func.name,
            args.len()
        )));
    }
    let tuple_reg = args[0];
    let index_reg = args[1];
    let index = state.reg_int_const.get(&index_reg.0).copied().ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported dynamic tuple index in {}: v{} is not a constant",
            func.name, index_reg.0
        ))
    })?;
    if index < 0 {
        return Err(CompileError::Codegen(format!(
            "VHDL backend tuple index out of range in {}: {}",
            func.name, index
        )));
    }
    let fields = state.reg_tuple_fields.get(&tuple_reg.0).ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported runtime tuple access in {}: v{} is not a virtual hardware aggregate",
            func.name, tuple_reg.0
        ))
    })?;
    let field = fields.get(index as usize).ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend tuple index out of range in {}: v{} has {} fields, requested {}",
            func.name,
            tuple_reg.0,
            fields.len(),
            index
        ))
    })?;
    state.reg_expr.insert(dest.0, field.expr.clone());
    state.reg_ty.insert(dest.0, field.ty);
    Ok(())
}

fn lower_vhdl_call(
    caller: &MirFunction,
    state: &mut VhdlLowerState,
    dest: Option<mir::VReg>,
    target: &CallTarget,
    args: &[mir::VReg],
    types: &TypeRegistry,
    entity_table: &BTreeMap<&str, &MirFunction>,
) -> Result<(), CompileError> {
    let callee_name = target.name();
    let callee = entity_table.get(callee_name).copied().ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported call in {}: `{}` is not an @hardware entity",
            caller.name, callee_name
        ))
    })?;
    if args.len() != callee.params.len() {
        return Err(CompileError::Codegen(format!(
            "VHDL backend call arity mismatch in {} calling {}: expected {}, got {}",
            caller.name,
            callee.name,
            callee.params.len(),
            args.len()
        )));
    }

    let dest = dest.ok_or_else(|| {
        CompileError::Codegen(format!(
            "VHDL backend unsupported void hardware call in {} to {}",
            caller.name, callee.name
        ))
    })?;
    let return_abi = vhdl_return_abi(callee, types)?;
    let callee_entity = sanitize_vhdl_ident(&callee.name);
    let instance_name = format!("u_{}_{}", callee_entity, state.call_ordinal);
    state.call_ordinal += 1;

    let mut maps = Vec::new();
    for (param, arg) in callee.params.iter().zip(args.iter()) {
        let arg_expr = reg_expr_for_type(&state.reg_expr, &state.reg_int_const, *arg, param.ty, types)?;
        maps.push((sanitize_vhdl_ident(&param.name), arg_expr));
    }

    match &return_abi {
        VhdlReturnAbi::Scalar(field) => {
            let signal = format!("{}_{}", instance_name, field.port_name);
            state.signals.insert((signal.clone(), field.ty));
            maps.push((field.port_name.clone(), signal.clone()));
            state.reg_expr.insert(dest.0, signal);
            state.reg_ty.insert(dest.0, field.ty);
        }
        VhdlReturnAbi::AnonymousTuple(fields) | VhdlReturnAbi::LabeledTuple(fields) => {
            let mut virtual_fields = Vec::with_capacity(fields.len());
            for (index, field) in fields.iter().enumerate() {
                let signal = format!("{}_{}", instance_name, field.port_name);
                state.signals.insert((signal.clone(), field.ty));
                maps.push((field.port_name.clone(), signal.clone()));
                virtual_fields.push(VhdlTupleFieldExpr {
                    index,
                    ty: field.ty,
                    expr: signal,
                });
            }
            state.reg_tuple_fields.insert(dest.0, virtual_fields);
            state.reg_ty.insert(dest.0, callee.return_type);
        }
    }

    let mut instance = format!("    {}: entity work.{}\n", instance_name, callee_entity);
    instance.push_str("        port map (\n");
    for (idx, (port, expr)) in maps.iter().enumerate() {
        let comma = if idx + 1 == maps.len() { "" } else { "," };
        instance.push_str(&format!("            {} => {}{}\n", port, expr, comma));
    }
    instance.push_str("        );");
    state.instances.push(instance);
    Ok(())
}

fn local_name(func: &MirFunction, index: usize) -> Result<&str, CompileError> {
    if index < func.params.len() {
        return Ok(&func.params[index].name);
    }
    let local_index = index - func.params.len();
    func.locals
        .get(local_index)
        .map(|local| local.name.as_str())
        .ok_or_else(|| CompileError::Codegen(format!("VHDL backend local index out of range: {}", index)))
}

fn reg_expr_for(reg_expr: &std::collections::HashMap<u32, String>, reg: mir::VReg) -> Result<String, CompileError> {
    reg_expr
        .get(&reg.0)
        .cloned()
        .ok_or_else(|| CompileError::Codegen(format!("VHDL backend has no expression for v{}", reg.0)))
}

fn reg_expr_for_type(
    reg_expr: &std::collections::HashMap<u32, String>,
    reg_int_const: &std::collections::HashMap<u32, i64>,
    reg: mir::VReg,
    ty: crate::hir::TypeId,
    types: &TypeRegistry,
) -> Result<String, CompileError> {
    if let Some(value) = reg_int_const.get(&reg.0) {
        return vhdl_int_literal(*value, ty, types);
    }
    reg_expr_for(reg_expr, reg)
}

fn vhdl_type(ty: crate::hir::TypeId, types: &TypeRegistry) -> Result<&'static str, CompileError> {
    if ty == crate::hir::TypeId::I32 {
        Ok("signed(31 downto 0)")
    } else if ty == crate::hir::TypeId::I64 {
        Ok("signed(63 downto 0)")
    } else if ty == crate::hir::TypeId::BOOL {
        Ok("std_logic")
    } else {
        let detail = types
            .get(ty)
            .map(format_vhdl_type_detail)
            .unwrap_or_else(|| "unregistered".to_string());
        Err(CompileError::Codegen(format!(
            "VHDL backend unsupported type id: {:?} ({})",
            ty, detail
        )))
    }
}

fn vhdl_int_literal(value: i64, ty: crate::hir::TypeId, types: &TypeRegistry) -> Result<String, CompileError> {
    if ty == crate::hir::TypeId::I32 {
        Ok(format!("to_signed({}, 32)", value))
    } else if ty == crate::hir::TypeId::I64 {
        Ok(format!("to_signed({}, 64)", value))
    } else {
        let detail = types
            .get(ty)
            .map(format_vhdl_type_detail)
            .unwrap_or_else(|| "unregistered".to_string());
        Err(CompileError::Codegen(format!(
            "VHDL backend cannot materialize integer literal for type id: {:?} ({})",
            ty, detail
        )))
    }
}

fn format_vhdl_type_detail(ty: &HirType) -> String {
    format!("{:?}", ty)
}

fn binop_result_type(op: BinOp, int_ty: crate::hir::TypeId) -> crate::hir::TypeId {
    match op {
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => crate::hir::TypeId::BOOL,
        _ => int_ty,
    }
}

fn vhdl_unaryop(op: &UnaryOp, operand: &str) -> Result<String, CompileError> {
    let expr = match op {
        UnaryOp::Neg => format!("-({})", operand),
        UnaryOp::Not | UnaryOp::BitNot => format!("not {}", operand),
    };
    Ok(expr)
}

fn vhdl_binop(op: &BinOp, left: &str, right: &str) -> Result<String, CompileError> {
    let expr = match op {
        BinOp::Add => format!("{} + {}", left, right),
        BinOp::Sub => format!("{} - {}", left, right),
        BinOp::Mul => format!("{} * {}", left, right),
        BinOp::BitAnd | BinOp::And => format!("{} and {}", left, right),
        BinOp::BitOr | BinOp::Or => format!("{} or {}", left, right),
        BinOp::BitXor => format!("{} xor {}", left, right),
        BinOp::Eq => format!("'1' when {} = {} else '0'", left, right),
        BinOp::NotEq => format!("'1' when {} /= {} else '0'", left, right),
        BinOp::Lt => format!("'1' when {} < {} else '0'", left, right),
        BinOp::Gt => format!("'1' when {} > {} else '0'", left, right),
        BinOp::LtEq => format!("'1' when {} <= {} else '0'", left, right),
        BinOp::GtEq => format!("'1' when {} >= {} else '0'", left, right),
        _ => {
            return Err(CompileError::Codegen(format!(
                "VHDL backend unsupported binary operator: {:?}",
                op
            )))
        }
    };
    Ok(expr)
}

fn sanitize_vhdl_ident(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if (idx == 0 && ch.is_ascii_alphabetic()) || (idx > 0 && (ch.is_ascii_alphanumeric() || ch == '_')) {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "unnamed".to_string()
    } else {
        out
    }
}

// =============================================================================
// PTX code generation from MIR
// =============================================================================

/// Generate PTX assembly text from a MIR module.
fn generate_ptx(module: &mir::MirModule) -> String {
    let mut out = String::new();
    out.push_str("//\n// Generated by Simple compiler (PTX backend)\n//\n");
    out.push_str(".version 7.8\n");
    out.push_str(".target sm_86\n");
    out.push_str(".address_size 64\n\n");

    // Check if any function is a kernel
    let has_kernels = module.functions.iter().any(|f| {
        f.attributes
            .iter()
            .any(|a| a == "gpu_kernel" || a == "kernel" || a == "cuda_kernel")
    });

    for func in &module.functions {
        let is_kernel = func
            .attributes
            .iter()
            .any(|a| a == "gpu_kernel" || a == "kernel" || a == "cuda_kernel");
        // Skip host-only functions (non-kernel functions that aren't called from kernels)
        // For now, emit all functions if there are no kernels, or only kernel + device functions
        if has_kernels && !is_kernel && func.name == "main" {
            out.push_str(&format!("// Skipped host function: {}\n\n", func.name));
            continue;
        }
        emit_ptx_function(&mut out, func);
    }

    out
}

/// Emit a single MIR function as PTX.
fn emit_ptx_function(out: &mut String, func: &MirFunction) {
    let is_kernel = func
        .attributes
        .iter()
        .any(|a| a == "gpu_kernel" || a == "kernel" || a == "cuda_kernel");

    // Function header
    if is_kernel {
        out.push_str(&format!(".visible .entry {}(\n", func.name));
    } else {
        out.push_str(&format!(".visible .func {}(\n", func.name));
    }

    // Parameters
    for (i, _param) in func.params.iter().enumerate() {
        let comma = if i + 1 < func.params.len() { "," } else { "" };
        out.push_str(&format!("    .param .s64 %param{}{}\n", i, comma));
    }
    out.push_str(")\n{\n");

    // Count total VRegs used to size register declarations
    let max_vreg = func
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter_map(|inst| match inst {
            MirInst::ConstInt { dest, .. }
            | MirInst::ConstFloat { dest, .. }
            | MirInst::ConstBool { dest, .. }
            | MirInst::Copy { dest, .. }
            | MirInst::Cast { dest, .. }
            | MirInst::LocalAddr { dest, .. }
            | MirInst::ConstString { dest, .. } => Some(dest.0),
            MirInst::BinOp { dest, .. } => Some(dest.0),
            MirInst::GpuGlobalId { dest, .. } | MirInst::GpuLocalId { dest, .. } | MirInst::GpuGroupId { dest, .. } => {
                Some(dest.0)
            }
            MirInst::GpuLoadF64 { dest, .. } | MirInst::GpuLoadI64 { dest, .. } => Some(dest.0),
            MirInst::Load { dest, .. } | MirInst::TupleLit { dest, .. } => Some(dest.0),
            _ => None,
        })
        .max()
        .unwrap_or(0);

    // Register declarations — size to actual usage + headroom for GPU temp regs (500+ zone)
    // temp_counter may grow during emission, so we allocate generously here.
    // The initial temp_counter starts at 528 and grows per GpuLoad/GpuStore.
    let reg_count = (max_vreg + 1).max(256).max(600);
    out.push_str(&format!("    .reg .s64 %rd<{}>;\n", reg_count));
    out.push_str(&format!("    .reg .s32 %r<{}>;\n", reg_count));
    out.push_str(&format!("    .reg .f64 %fd<{}>;\n", reg_count));
    out.push_str(&format!("    .reg .f32 %f<{}>;\n", reg_count));
    out.push_str(&format!("    .reg .pred %p<{}>;\n", reg_count));

    // Local memory for function locals (used by LocalAddr + Load/Store pattern)
    let num_locals = func.params.len() + func.locals.len();
    if num_locals > 0 {
        out.push_str(&format!("    .local .align 8 .b8 __locals[{}];\n", num_locals * 8));
    }
    out.push('\n');

    // Load parameters into local memory slots
    for (i, _param) in func.params.iter().enumerate() {
        out.push_str(&format!("    ld.param.s64 %rd{}, [%param{}];\n", i, i));
        out.push_str(&format!("    st.local.s64 [__locals+{}], %rd{};\n", i * 8, i));
    }
    if !func.params.is_empty() {
        out.push('\n');
    }

    // Register provenance tracking for local vs global memory
    let mut reg_info = PtxRegInfo::new();

    // Basic blocks
    for (block_idx, block) in func.blocks.iter().enumerate() {
        out.push_str(&format!("BB{}:\n", block.id.0));

        for inst in &block.instructions {
            emit_ptx_instruction(out, inst, &mut reg_info);
        }

        emit_ptx_terminator(out, &block.terminator, is_kernel, block_idx);
        out.push('\n');
    }

    out.push_str("}\n\n");
}

/// Virtual register type for PTX code generation.
/// PTX uses distinct register files for integers, floats, and predicates.
#[derive(Debug, Clone, Copy, PartialEq)]
enum PtxVRegType {
    I64,
    F64,
    Pred,
}

/// Track which VRegs hold local addresses (from LocalAddr) vs global addresses (from params/GEP),
/// and the type of each VReg for correct register file selection in PTX.
struct PtxRegInfo {
    /// VRegs that hold local memory addresses (produced by LocalAddr)
    local_regs: std::collections::HashSet<u32>,
    /// Type of each VReg (I64, F64, or Pred)
    vreg_types: std::collections::HashMap<u32, PtxVRegType>,
    /// Counter for temporary registers, starts at 528 to avoid collisions with
    /// the 500-527 zone used by GPU intrinsics (GpuGlobalId, GpuLocalId, etc.)
    temp_counter: u32,
    /// Maps LocalAddr vregs to their byte offset in __locals
    local_vreg_offset: std::collections::HashMap<u32, usize>,
    /// Maps local byte offsets to the type stored there (for f64 propagation)
    local_offset_types: std::collections::HashMap<usize, PtxVRegType>,
}

impl PtxRegInfo {
    fn new() -> Self {
        Self {
            local_regs: std::collections::HashSet::new(),
            vreg_types: std::collections::HashMap::new(),
            temp_counter: 528,
            local_vreg_offset: std::collections::HashMap::new(),
            local_offset_types: std::collections::HashMap::new(),
        }
    }

    fn mark_local(&mut self, vreg: u32, offset: usize) {
        self.local_regs.insert(vreg);
        self.local_vreg_offset.insert(vreg, offset);
    }

    fn is_local(&self, vreg: u32) -> bool {
        self.local_regs.contains(&vreg)
    }

    /// Record that a local offset holds a particular type.
    fn set_local_type(&mut self, addr_vreg: u32, ty: PtxVRegType) {
        if let Some(&offset) = self.local_vreg_offset.get(&addr_vreg) {
            self.local_offset_types.insert(offset, ty);
        }
    }

    /// Get the type stored at a local offset (via addr vreg), defaulting to I64.
    fn get_local_type(&self, addr_vreg: u32) -> PtxVRegType {
        self.local_vreg_offset
            .get(&addr_vreg)
            .and_then(|offset| self.local_offset_types.get(offset))
            .copied()
            .unwrap_or(PtxVRegType::I64)
    }

    /// Set the type of a virtual register.
    fn set_type(&mut self, vreg: u32, ty: PtxVRegType) {
        self.vreg_types.insert(vreg, ty);
    }

    /// Get the type of a virtual register, defaulting to I64.
    fn get_type(&self, vreg: u32) -> PtxVRegType {
        self.vreg_types.get(&vreg).copied().unwrap_or(PtxVRegType::I64)
    }

    /// Allocate a temporary register index and return it, incrementing the counter.
    fn next_temp(&mut self) -> u32 {
        let t = self.temp_counter;
        self.temp_counter += 1;
        t
    }

    /// Return the PTX register name prefix for a given VReg based on its type.
    fn reg_name(&self, vreg: u32) -> String {
        match self.get_type(vreg) {
            PtxVRegType::I64 => format!("%rd{}", vreg),
            PtxVRegType::F64 => format!("%fd{}", vreg),
            PtxVRegType::Pred => format!("%p{}", vreg),
        }
    }
}

/// Emit a single MIR instruction as PTX.
fn emit_ptx_instruction(out: &mut String, inst: &MirInst, reg_info: &mut PtxRegInfo) {
    match inst {
        // ---- Constants ----
        MirInst::ConstInt { dest, value } => {
            out.push_str(&format!("    mov.s64 %rd{}, {};\n", dest.0, value));
        }
        MirInst::ConstFloat { dest, value } => {
            // PTX requires double-precision hex or decimal float notation
            let bits = value.to_bits();
            out.push_str(&format!("    mov.f64 %fd{}, 0d{:016X};\n", dest.0, bits));
            reg_info.set_type(dest.0, PtxVRegType::F64);
        }
        MirInst::ConstBool { dest, value } => {
            let val = if *value { 1 } else { 0 };
            out.push_str(&format!("    setp.ne.s32 %p{}, {}, 0;\n", dest.0, val));
            reg_info.set_type(dest.0, PtxVRegType::Pred);
        }

        // ---- Copy ----
        MirInst::Copy { dest, src } => match reg_info.get_type(src.0) {
            PtxVRegType::F64 => {
                out.push_str(&format!("    mov.f64 %fd{}, %fd{};\n", dest.0, src.0));
                reg_info.set_type(dest.0, PtxVRegType::F64);
            }
            PtxVRegType::Pred => {
                out.push_str(&format!("    mov.pred %p{}, %p{};\n", dest.0, src.0));
                reg_info.set_type(dest.0, PtxVRegType::Pred);
            }
            PtxVRegType::I64 => {
                out.push_str(&format!("    mov.s64 %rd{}, %rd{};\n", dest.0, src.0));
            }
        },

        // ---- Binary operations ----
        MirInst::BinOp { dest, op, left, right } => {
            let is_float =
                reg_info.get_type(left.0) == PtxVRegType::F64 || reg_info.get_type(right.0) == PtxVRegType::F64;

            match op {
                // Comparison ops: emit setp instruction, result in predicate register
                BinOp::Lt => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.lt.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.lt.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::LtEq => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.le.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.le.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::Gt => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.gt.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.gt.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::GtEq => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.ge.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.ge.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::Eq => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.eq.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.eq.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::NotEq => {
                    if is_float {
                        out.push_str(&format!(
                            "    setp.ne.f64 %p{}, %fd{}, %fd{};\n",
                            dest.0, left.0, right.0
                        ));
                    } else {
                        out.push_str(&format!(
                            "    setp.ne.s64 %p{}, %rd{}, %rd{};\n",
                            dest.0, left.0, right.0
                        ));
                    }
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::And => {
                    out.push_str(&format!("    and.pred %p{}, %p{}, %p{};\n", dest.0, left.0, right.0));
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                BinOp::Or => {
                    out.push_str(&format!("    or.pred %p{}, %p{}, %p{};\n", dest.0, left.0, right.0));
                    reg_info.set_type(dest.0, PtxVRegType::Pred);
                }
                _ => {
                    if is_float {
                        let ptx_op = match op {
                            BinOp::Add => "add.f64",
                            BinOp::Sub => "sub.f64",
                            BinOp::Mul => "mul.f64",
                            BinOp::Div => "div.rn.f64",
                            other => {
                                out.push_str(&format!("    // unsupported float binop: {:?}\n", other));
                                return;
                            }
                        };
                        out.push_str(&format!(
                            "    {} %fd{}, %fd{}, %fd{};\n",
                            ptx_op, dest.0, left.0, right.0
                        ));
                        reg_info.set_type(dest.0, PtxVRegType::F64);
                    } else {
                        let ptx_op = match op {
                            BinOp::Add => "add.s64",
                            BinOp::Sub => "sub.s64",
                            BinOp::Mul => "mul.lo.s64",
                            BinOp::Div => "div.s64",
                            BinOp::Mod => "rem.s64",
                            BinOp::BitAnd => "and.b64",
                            BinOp::BitOr => "or.b64",
                            BinOp::BitXor => "xor.b64",
                            BinOp::ShiftLeft => "shl.b64",
                            BinOp::ShiftRight => "shr.s64",
                            other => {
                                out.push_str(&format!("    // unsupported binop: {:?}\n", other));
                                return;
                            }
                        };
                        out.push_str(&format!(
                            "    {} %rd{}, %rd{}, %rd{};\n",
                            ptx_op, dest.0, left.0, right.0
                        ));
                    }
                }
            }
        }

        // ---- Unary operations ----
        MirInst::UnaryOp { dest, op, operand } => match op {
            UnaryOp::Neg => {
                out.push_str(&format!("    neg.s64 %rd{}, %rd{};\n", dest.0, operand.0));
            }
            UnaryOp::Not => {
                out.push_str(&format!("    not.pred %p{}, %p{};\n", dest.0, operand.0));
            }
            other => {
                out.push_str(&format!("    // unsupported unary: {:?}\n", other));
            }
        },

        // ---- Cast ----
        MirInst::Cast { dest, source, .. } => {
            out.push_str(&format!("    mov.s64 %rd{}, %rd{};\n", dest.0, source.0));
        }

        // ---- Function calls ----
        MirInst::Call { dest, target, args } => {
            let func_name = target.name();
            if let Some(d) = dest {
                out.push_str(&format!("    call.uni (%rd{}), {}", d.0, func_name));
            } else {
                out.push_str(&format!("    call.uni {}", func_name));
            }
            if !args.is_empty() {
                out.push_str(", (");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!("%rd{}", arg.0));
                }
                out.push(')');
            }
            out.push_str(";\n");
        }

        // ---- Local variable access ----
        MirInst::LocalAddr { dest, local_index } => {
            // Compute address into local memory: __locals + local_index * 8
            let offset = local_index * 8;
            out.push_str(&format!("    mov.s64 %rd{}, __locals;\n", dest.0));
            if offset > 0 {
                out.push_str(&format!("    add.s64 %rd{}, %rd{}, {};\n", dest.0, dest.0, offset));
            }
            reg_info.mark_local(dest.0, offset);
        }

        // ---- Global loads/stores ----
        MirInst::GlobalLoad { dest, global_name, .. } => {
            out.push_str(&format!("    // global_load %rd{} = {}\n", dest.0, global_name));
            out.push_str(&format!("    ld.global.s64 %rd{}, [{}];\n", dest.0, global_name));
        }
        MirInst::GlobalStore { global_name, value, .. } => {
            out.push_str(&format!("    st.global.s64 [{}], %rd{};\n", global_name, value.0));
        }

        // ---- Constants ----
        MirInst::ConstString { dest, value } => {
            // Strings in PTX are stored as global .const arrays
            out.push_str(&format!("    // const_string %rd{} = {:?}\n", dest.0, value));
            out.push_str(&format!("    mov.s64 %rd{}, 0; // string placeholder\n", dest.0));
        }

        // ---- Tuple/Unit ----
        MirInst::TupleLit { dest, elements } => {
            if elements.is_empty() {
                // Unit value ()
                out.push_str(&format!("    mov.s64 %rd{}, 0; // unit ()\n", dest.0));
            } else {
                out.push_str(&format!("    // tuple(%rd{}, {} elements)\n", dest.0, elements.len()));
                out.push_str(&format!("    mov.s64 %rd{}, 0; // tuple placeholder\n", dest.0));
            }
        }

        // ---- Struct init ----
        MirInst::StructInit { dest, .. } => {
            out.push_str(&format!("    mov.s64 %rd{}, 0; // struct init placeholder\n", dest.0));
        }

        // ---- No-op instructions for PTX ----
        MirInst::Drop { .. } | MirInst::EndScope { .. } => {
            // No-op in PTX
        }

        // ---- GPU intrinsics ----
        MirInst::GpuGlobalId { dest, dim } => {
            let (tid, ntid, ctaid) = match dim {
                0 => ("%tid.x", "%ntid.x", "%ctaid.x"),
                1 => ("%tid.y", "%ntid.y", "%ctaid.y"),
                2 => ("%tid.z", "%ntid.z", "%ctaid.z"),
                _ => ("%tid.x", "%ntid.x", "%ctaid.x"),
            };
            // global_id = ctaid * ntid + tid
            // Use dedicated temp registers in 500+ zone to avoid conflicts
            let d = dest.0;
            let t_tid = 500 + *dim as usize * 3;
            let t_ntid = t_tid + 1;
            let t_ctaid = t_tid + 2;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t_tid, tid));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", t_tid, t_tid));
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t_ntid, ntid));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", t_ntid, t_ntid));
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t_ctaid, ctaid));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", t_ctaid, t_ctaid));
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, %rd{}, %rd{};\n",
                d, t_ctaid, t_ntid, t_tid
            ));
        }
        MirInst::GpuLocalId { dest, dim } => {
            let reg = match dim {
                0 => "%tid.x",
                1 => "%tid.y",
                2 => "%tid.z",
                _ => "%tid.x",
            };
            let t = 510 + *dim as usize;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t, reg));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", dest.0, t));
        }
        MirInst::GpuGroupId { dest, dim } => {
            let reg = match dim {
                0 => "%ctaid.x",
                1 => "%ctaid.y",
                2 => "%ctaid.z",
                _ => "%ctaid.x",
            };
            let t = 513 + *dim as usize;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t, reg));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", dest.0, t));
        }
        MirInst::GpuGlobalSize { dest, dim } => {
            // global_size = nctaid * ntid
            let (ntid, nctaid) = match dim {
                0 => ("%ntid.x", "%nctaid.x"),
                1 => ("%ntid.y", "%nctaid.y"),
                2 => ("%ntid.z", "%nctaid.z"),
                _ => ("%ntid.x", "%nctaid.x"),
            };
            let t1 = 516 + *dim as usize * 2;
            let t2 = t1 + 1;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t1, nctaid));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", t1, t1));
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t2, ntid));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", t2, t2));
            out.push_str(&format!("    mul.lo.s64 %rd{}, %rd{}, %rd{};\n", dest.0, t1, t2));
        }
        MirInst::GpuLocalSize { dest, dim } => {
            let reg = match dim {
                0 => "%ntid.x",
                1 => "%ntid.y",
                2 => "%ntid.z",
                _ => "%ntid.x",
            };
            let t = 522 + *dim as usize;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t, reg));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", dest.0, t));
        }
        MirInst::GpuNumGroups { dest, dim } => {
            let reg = match dim {
                0 => "%nctaid.x",
                1 => "%nctaid.y",
                2 => "%nctaid.z",
                _ => "%nctaid.x",
            };
            let t = 525 + *dim as usize;
            out.push_str(&format!("    mov.u32 %r{}, {};\n", t, reg));
            out.push_str(&format!("    cvt.s64.u32 %rd{}, %r{};\n", dest.0, t));
        }
        MirInst::GpuBarrier => {
            out.push_str("    bar.sync 0;\n");
        }
        MirInst::GpuMemFence { scope } => {
            let fence = match scope {
                GpuMemoryScope::WorkGroup => "membar.cta",
                GpuMemoryScope::Device => "membar.gl",
                GpuMemoryScope::All => "membar.sys",
            };
            out.push_str(&format!("    {};\n", fence));
        }
        MirInst::GpuSharedAlloc { dest, size, .. } => {
            out.push_str(&format!("    // shared memory alloc: %rd{} = {} bytes\n", dest.0, size));
            out.push_str(&format!("    .shared .align 8 .b8 __shared_{}[{}];\n", dest.0, size));
        }

        // ---- GPU typed memory access ----
        MirInst::GpuLoadF64 { dest, ptr, index } => {
            let addr_tmp = reg_info.next_temp();
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, 8, %rd{};\n",
                addr_tmp, index.0, ptr.0
            ));
            out.push_str(&format!("    ld.global.f64 %fd{}, [%rd{}];\n", dest.0, addr_tmp));
            reg_info.set_type(dest.0, PtxVRegType::F64);
        }
        MirInst::GpuStoreF64 { ptr, index, value } => {
            let addr_tmp = reg_info.next_temp();
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, 8, %rd{};\n",
                addr_tmp, index.0, ptr.0
            ));
            out.push_str(&format!("    st.global.f64 [%rd{}], %fd{};\n", addr_tmp, value.0));
        }
        MirInst::GpuLoadI64 { dest, ptr, index } => {
            let addr_tmp = reg_info.next_temp();
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, 8, %rd{};\n",
                addr_tmp, index.0, ptr.0
            ));
            out.push_str(&format!("    ld.global.s64 %rd{}, [%rd{}];\n", dest.0, addr_tmp));
        }
        MirInst::GpuStoreI64 { ptr, index, value } => {
            let addr_tmp = reg_info.next_temp();
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, 8, %rd{};\n",
                addr_tmp, index.0, ptr.0
            ));
            out.push_str(&format!("    st.global.s64 [%rd{}], %rd{};\n", addr_tmp, value.0));
        }

        // ---- Memory ----
        MirInst::Load { dest, addr, .. } => {
            // Use local state space for LocalAddr-derived addresses, global otherwise
            if reg_info.is_local(addr.0) {
                let local_type = reg_info.get_local_type(addr.0);
                match local_type {
                    PtxVRegType::F64 => {
                        out.push_str(&format!("    ld.local.f64 %fd{}, [%rd{}];\n", dest.0, addr.0));
                        reg_info.set_type(dest.0, PtxVRegType::F64);
                    }
                    _ => {
                        out.push_str(&format!("    ld.local.s64 %rd{}, [%rd{}];\n", dest.0, addr.0));
                    }
                }
            } else {
                out.push_str(&format!("    ld.global.s64 %rd{}, [%rd{}];\n", dest.0, addr.0));
            }
        }
        MirInst::Store { addr, value, .. } => {
            let val_type = reg_info.get_type(value.0);
            if reg_info.is_local(addr.0) {
                // Track type stored at this local offset for later Load
                reg_info.set_local_type(addr.0, val_type);
                match val_type {
                    PtxVRegType::F64 => {
                        out.push_str(&format!("    st.local.f64 [%rd{}], %fd{};\n", addr.0, value.0));
                    }
                    _ => {
                        out.push_str(&format!("    st.local.s64 [%rd{}], %rd{};\n", addr.0, value.0));
                    }
                }
            } else {
                match val_type {
                    PtxVRegType::F64 => {
                        out.push_str(&format!("    st.global.f64 [%rd{}], %fd{};\n", addr.0, value.0));
                    }
                    _ => {
                        out.push_str(&format!("    st.global.s64 [%rd{}], %rd{};\n", addr.0, value.0));
                    }
                }
            }
        }
        MirInst::GetElementPtr { dest, base, index } => {
            // Assume 8-byte elements (s64)
            // GEP from a global base produces a global address
            out.push_str(&format!(
                "    mad.lo.s64 %rd{}, %rd{}, 8, %rd{};\n",
                dest.0, index.0, base.0
            ));
            // Propagate memory space: if base is local, result is local; otherwise global
            // Use usize::MAX as sentinel offset — GEP-derived addresses won't match
            // specific local offsets for type propagation, falling back to s64
            if reg_info.is_local(base.0) {
                reg_info.mark_local(dest.0, usize::MAX);
            }
        }

        // ---- All other instructions: emit as comment ----
        other => {
            out.push_str(&format!("    // [unsupported] {:?}\n", std::mem::discriminant(other)));
        }
    }
}

/// Emit a block terminator as PTX.
fn emit_ptx_terminator(out: &mut String, term: &Terminator, is_kernel: bool, _block_idx: usize) {
    match term {
        Terminator::Return(Some(vreg)) => {
            if is_kernel {
                out.push_str("    exit;\n");
            } else {
                out.push_str(&format!("    // return %rd{}\n", vreg.0));
                out.push_str("    ret;\n");
            }
        }
        Terminator::Return(None) => {
            if is_kernel {
                out.push_str("    exit;\n");
            } else {
                out.push_str("    ret;\n");
            }
        }
        Terminator::Jump(target) => {
            out.push_str(&format!("    bra BB{};\n", target.0));
        }
        Terminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            out.push_str(&format!("    @%p{} bra BB{};\n", cond.0, then_block.0));
            out.push_str(&format!("    bra BB{};\n", else_block.0));
        }
        Terminator::Unreachable => {
            out.push_str("    // unreachable\n");
            out.push_str("    trap;\n");
        }
    }
}

fn select_backend(target: &Target) -> Result<BackendKind, CompileError> {
    let mut backend = BackendKind::for_target(target);

    // SIMPLE_FORCE_LLVM takes precedence over SIMPLE_BACKEND
    let force_llvm = env::var("SIMPLE_FORCE_LLVM")
        .map(|v| matches!(v.to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on"))
        .unwrap_or(false);

    if force_llvm {
        if cfg!(feature = "llvm") {
            backend = BackendKind::Llvm;
        } else {
            return Err(CompileError::Codegen(
                "SIMPLE_FORCE_LLVM is set but this build does not include the 'llvm' feature".to_string(),
            ));
        }
    }

    if let Ok(value) = env::var("SIMPLE_BACKEND") {
        let value = value.to_ascii_lowercase();
        backend = match value.as_str() {
            "auto" => BackendKind::for_target(target),
            "cranelift" => BackendKind::Cranelift,
            "llvm" => {
                if cfg!(feature = "llvm") {
                    BackendKind::Llvm
                } else {
                    return Err(CompileError::Codegen(
                        "SIMPLE_BACKEND=llvm but compiler was built without --features llvm".to_string(),
                    ));
                }
            }
            other => {
                return Err(CompileError::Codegen(format!(
                    "unknown SIMPLE_BACKEND '{}', expected auto|cranelift|llvm",
                    other
                )))
            }
        };
    }

    Ok(backend)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;
    #[cfg(feature = "cuda")]
    use std::ffi::CString;
    use tempfile::NamedTempFile;

    #[test]
    fn backend_env_defaults_to_target_selection() {
        env::remove_var("SIMPLE_BACKEND");
        env::remove_var("SIMPLE_FORCE_LLVM");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::for_target(&target));
    }

    #[test]
    fn backend_env_respects_cranelift_override() {
        env::set_var("SIMPLE_BACKEND", "cranelift");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::Cranelift);
        env::remove_var("SIMPLE_BACKEND");
    }

    #[test]
    #[cfg(feature = "llvm")]
    fn backend_env_respects_llvm_override() {
        env::set_var("SIMPLE_BACKEND", "llvm");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::Llvm);
        env::remove_var("SIMPLE_BACKEND");
    }

    #[test]
    fn backend_env_unknown_value_errors() {
        env::set_var("SIMPLE_BACKEND", "unknown-backend");
        let target = Target::host();
        let result = select_backend(&target);
        assert!(result.is_err());
        env::remove_var("SIMPLE_BACKEND");
    }

    #[test]
    fn ptx_emits_documented_gpu_aliases_without_undefined_store_regs() {
        let source = r#"
@gpu_kernel
fn vector_add(a: i64, b: i64, out: i64, n: i64):
    val idx = gpu_thread_id_x() + gpu_block_id_x() * gpu_block_dim_x()
    if idx < n:
        val av = gpu_load_f64(a, idx)
        val bv = gpu_load_f64(b, idx)
        gpu_store_f64(out, idx, av + bv)
"#;

        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let ptx = generate_ptx(&mir_module);

        assert!(
            ptx.contains("mov.u32 %r510, %tid.x;"),
            "expected gpu_thread_id_x alias to lower to %tid.x:\n{ptx}"
        );
        assert!(
            ptx.contains("mov.s64 %rd32, 3;"),
            "expected void gpu_store_f64 to materialize nil:\n{ptx}"
        );
        assert!(
            !ptx.contains("%rd28;"),
            "unexpected undefined-register artifact remains in PTX:\n{ptx}"
        );
        assert!(
            !ptx.contains("call.uni (%rd0), gpu_thread_id_x;"),
            "gpu_thread_id_x should not remain as a call target:\n{ptx}"
        );
    }

    #[test]
    fn vhdl_emits_combinational_adder_from_simple_source() {
        let source = "@hardware\nfn add(a: i32, b: i32) -> i32:\n    return a + b\n";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(vhdl.contains("entity add is"), "expected add entity:\n{vhdl}");
        assert!(
            vhdl.contains("a : in signed(31 downto 0);"),
            "expected i32 input a:\n{vhdl}"
        );
        assert!(
            vhdl.contains("b : in signed(31 downto 0);"),
            "expected i32 input b:\n{vhdl}"
        );
        assert!(
            vhdl.contains("result_out : out signed(31 downto 0)"),
            "expected i32 result:\n{vhdl}"
        );
        assert!(vhdl.contains("<= a + b;"), "expected combinational add:\n{vhdl}");
    }

    #[test]
    fn vhdl_emits_typed_constants_unary_ops_and_const_compare() {
        let source = "\
@hardware
fn one() -> i32:
    return 1

@hardware
fn neg(a: i32) -> i32:
    return -a

@hardware
fn inv(a: bool) -> bool:
    return not a

@hardware
fn is_one(a: i32) -> bool:
    return a == 1
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("result_out <= to_signed(1, 32);"),
            "expected typed signed constant:\n{vhdl}"
        );
        assert!(vhdl.contains("<= -(a);"), "expected unary negation:\n{vhdl}");
        assert!(vhdl.contains("<= not a;"), "expected boolean not:\n{vhdl}");
        assert!(
            vhdl.contains("<= '1' when a = to_signed(1, 32) else '0';"),
            "expected typed constant comparison:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_emits_simple_if_else_return_mux() {
        let source = "\
@hardware
fn sel(flag: bool, a: i32, b: i32) -> i32:
    if flag:
        return a
    else:
        return b
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("result_out <= a when flag = '1' else b;"),
            "expected if/else result mux:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_emits_only_hardware_functions() {
        let source = "\
fn helper(a: i32) -> i32:
    return a + 1

@hardware
fn top(a: i32) -> i32:
    return a
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(vhdl.contains("entity top is"), "expected top entity:\n{vhdl}");
        assert!(
            !vhdl.contains("entity helper is"),
            "helper must not be emitted:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_lowers_scalar_hardware_call_to_entity_instance() {
        let source = "\
@hardware
fn inc(a: i32) -> i32:
    return a + 1

@hardware
fn top(a: i32) -> i32:
    return inc(a)
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("signal u_inc_0_result_out : signed(31 downto 0);"),
            "expected deterministic scalar call output signal:\n{vhdl}"
        );
        assert!(
            vhdl.contains("u_inc_0: entity work.inc"),
            "expected inc entity instance:\n{vhdl}"
        );
        assert!(vhdl.contains("a => a"), "expected input port map:\n{vhdl}");
        assert!(
            vhdl.contains("result_out => u_inc_0_result_out"),
            "expected output port map:\n{vhdl}"
        );
        assert!(
            vhdl.contains("result_out <= u_inc_0_result_out;"),
            "expected top return assignment from call signal:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_lowers_multi_output_hardware_call_to_named_port_map() {
        let source = "\
@hardware
fn full_add(a: bool, b: bool) -> (sum: bool, cout: bool):
    return (sum: a xor b, cout: a and b)

@hardware
fn top(a: bool, b: bool) -> (sum0: bool, carry: bool):
    return (sum0: full_add(a, b).sum, carry: full_add(a, b).cout)
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("signal u_full_add_0_sum : std_logic;"),
            "expected deterministic sum temp signal:\n{vhdl}"
        );
        assert!(
            vhdl.contains("signal u_full_add_0_cout : std_logic;"),
            "expected deterministic cout temp signal:\n{vhdl}"
        );
        assert!(
            vhdl.contains("u_full_add_0: entity work.full_add"),
            "expected full_add entity instance:\n{vhdl}"
        );
        assert!(
            vhdl.contains("sum => u_full_add_0_sum"),
            "expected sum port map:\n{vhdl}"
        );
        assert!(
            vhdl.contains("cout => u_full_add_0_cout"),
            "expected cout port map:\n{vhdl}"
        );
        assert!(
            vhdl.contains("sum0 <= u_full_add_0_sum;"),
            "expected sum projection:\n{vhdl}"
        );
        assert!(
            vhdl.contains("carry <= u_full_add_1_cout;"),
            "expected carry projection from second call:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_decomposes_labeled_tuple_return_assignments() {
        let source = "\
@hardware
fn full_add(a: bool, b: bool) -> (sum: bool, cout: bool):
    return (sum: a, cout: b)
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(vhdl.contains("sum : out std_logic;"), "expected sum output:\n{vhdl}");
        assert!(vhdl.contains("cout : out std_logic"), "expected cout output:\n{vhdl}");
        assert!(vhdl.contains("sum <= a;"), "expected sum assignment:\n{vhdl}");
        assert!(vhdl.contains("cout <= b;"), "expected cout assignment:\n{vhdl}");
        assert!(
            !vhdl.contains("result_out"),
            "tuple return should not use scalar result_out:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_decomposes_anonymous_tuple_return_assignments() {
        let source = "\
@hardware
fn bounds(x: i32, zero: bool) -> (i32, bool):
    return (x, zero)
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("out0 : out signed(31 downto 0);"),
            "expected out0 output:\n{vhdl}"
        );
        assert!(vhdl.contains("out1 : out std_logic"), "expected out1 output:\n{vhdl}");
        assert!(vhdl.contains("out0 <= x;"), "expected out0 assignment:\n{vhdl}");
        assert!(vhdl.contains("out1 <= zero;"), "expected out1 assignment:\n{vhdl}");
    }

    #[test]
    fn vhdl_decomposes_labeled_tuple_branch_return_assignments() {
        let source = "\
@hardware
fn choose(flag: bool, a: bool, b: bool) -> (sum: bool, cout: bool):
    if flag:
        return (sum: a, cout: b)
    else:
        return (sum: b, cout: a)
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("sum <= a when flag = '1' else b;"),
            "expected sum branch assignment:\n{vhdl}"
        );
        assert!(
            vhdl.contains("cout <= b when flag = '1' else a;"),
            "expected cout branch assignment:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_lowers_labeled_hardware_call_field_access_to_output_signal() {
        let source = "\
@hardware
fn pair(a: bool, b: bool) -> (left: bool, right: bool):
    return (left: a, right: b)

@hardware
fn top(a: bool, b: bool) -> bool:
    return pair(a, b).right
";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
        let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
        let vhdl = generate_vhdl(&mir_module).expect("VHDL generation failed");

        assert!(
            vhdl.contains("right : out std_logic"),
            "expected labeled tuple output port:\n{vhdl}"
        );
        assert!(
            vhdl.contains("signal u_pair_0_right : std_logic;"),
            "expected deterministic field temp signal:\n{vhdl}"
        );
        assert!(
            vhdl.contains("right => u_pair_0_right"),
            "expected pair output port map:\n{vhdl}"
        );
        assert!(
            vhdl.contains("result_out <= u_pair_0_right;"),
            "expected tuple field projection to drive scalar return:\n{vhdl}"
        );
    }

    #[test]
    fn vhdl_return_abi_uses_labeled_tuple_ports() {
        let mut types = TypeRegistry::new();
        let return_ty = types.register(HirType::LabeledTuple(vec![
            ("sum".to_string(), crate::hir::TypeId::BOOL),
            ("carry-out".to_string(), crate::hir::TypeId::BOOL),
        ]));
        let func = MirFunction::new(
            "full_add".to_string(),
            return_ty,
            simple_parser::ast::Visibility::Private,
        );

        let abi = vhdl_return_abi(&func, &types).expect("return ABI");
        assert_eq!(
            abi.ports()
                .iter()
                .map(|port| (port.name.as_str(), port.direction.as_vhdl(), port.ty))
                .collect::<Vec<_>>(),
            vec![
                ("sum", "out", crate::hir::TypeId::BOOL),
                ("carry_out", "out", crate::hir::TypeId::BOOL),
            ]
        );
    }

    #[test]
    fn vhdl_return_abi_uses_deterministic_anonymous_tuple_ports() {
        let mut types = TypeRegistry::new();
        let return_ty = types.register(HirType::Tuple(vec![crate::hir::TypeId::I32, crate::hir::TypeId::BOOL]));
        let func = MirFunction::new("bounds".to_string(), return_ty, simple_parser::ast::Visibility::Private);

        let abi = vhdl_return_abi(&func, &types).expect("return ABI");
        assert_eq!(
            abi.ports()
                .iter()
                .map(|port| (port.name.as_str(), port.direction.as_vhdl(), port.ty))
                .collect::<Vec<_>>(),
            vec![
                ("out0", "out", crate::hir::TypeId::I32),
                ("out1", "out", crate::hir::TypeId::BOOL),
            ]
        );
    }

    #[test]
    fn vhdl_port_validation_rejects_sanitized_collisions() {
        let ports = vec![
            VhdlPort::input(
                "carry_out".to_string(),
                "carry-out".to_string(),
                crate::hir::TypeId::BOOL,
            ),
            VhdlPort::output(
                "carry_out".to_string(),
                "carry_out".to_string(),
                crate::hir::TypeId::BOOL,
            ),
        ];

        let err = validate_vhdl_port_names("full_add", "full_add", &ports).expect_err("collision");
        assert!(
            format!("{err}").contains("VHDL identifier collision after sanitization"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn vhdl_rt_tuple_get_projects_constant_index_from_virtual_tuple() {
        let types = TypeRegistry::new();
        let func = MirFunction::new(
            "uses_full_add".to_string(),
            crate::hir::TypeId::BOOL,
            simple_parser::ast::Visibility::Private,
        );
        let mut state = VhdlLowerState::default();
        state.reg_tuple_fields.insert(
            1,
            vec![
                VhdlTupleFieldExpr {
                    index: 0,
                    ty: crate::hir::TypeId::BOOL,
                    expr: "u_full_add_0_sum".to_string(),
                },
                VhdlTupleFieldExpr {
                    index: 1,
                    ty: crate::hir::TypeId::BOOL,
                    expr: "u_full_add_0_cout".to_string(),
                },
            ],
        );
        state.reg_ty.insert(1, func.return_type);
        state.reg_int_const.insert(2, 1);

        lower_vhdl_instruction(
            &func,
            &mut state,
            &MirInst::Call {
                dest: Some(crate::mir::VReg(3)),
                target: CallTarget::from_name("rt_tuple_get"),
                args: vec![crate::mir::VReg(1), crate::mir::VReg(2)],
            },
            &types,
            &BTreeMap::new(),
        )
        .expect("tuple projection");

        assert_eq!(state.reg_expr.get(&3).map(String::as_str), Some("u_full_add_0_cout"));
        assert_eq!(state.reg_ty.get(&3).copied(), Some(crate::hir::TypeId::BOOL));
    }

    #[test]
    fn vhdl_rt_tuple_get_rejects_dynamic_index() {
        let func = MirFunction::new(
            "uses_full_add".to_string(),
            crate::hir::TypeId::BOOL,
            simple_parser::ast::Visibility::Private,
        );
        let mut state = VhdlLowerState::default();
        state.reg_tuple_fields.insert(
            1,
            vec![VhdlTupleFieldExpr {
                index: 0,
                ty: crate::hir::TypeId::BOOL,
                expr: "u_full_add_0_sum".to_string(),
            }],
        );

        let err = lower_vhdl_tuple_get(
            &func,
            &mut state,
            Some(crate::mir::VReg(3)),
            &[crate::mir::VReg(1), crate::mir::VReg(2)],
        )
        .expect_err("dynamic tuple index should be rejected");

        let message = format!("{err}");
        assert!(
            message.contains("unsupported dynamic tuple index"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn vhdl_rt_tuple_get_rejects_non_virtual_tuple_receiver() {
        let func = MirFunction::new(
            "uses_full_add".to_string(),
            crate::hir::TypeId::BOOL,
            simple_parser::ast::Visibility::Private,
        );
        let mut state = VhdlLowerState::default();
        state.reg_int_const.insert(2, 0);

        let err = lower_vhdl_tuple_get(
            &func,
            &mut state,
            Some(crate::mir::VReg(3)),
            &[crate::mir::VReg(1), crate::mir::VReg(2)],
        )
        .expect_err("non-virtual tuple receiver should be rejected");

        let message = format!("{err}");
        assert!(
            message.contains("unsupported runtime tuple access"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn compile_file_to_vhdl_writes_vhdl_output() {
        let source_file = NamedTempFile::new().expect("temp source");
        std::fs::write(
            source_file.path(),
            "@hardware\nfn add(a: i32, b: i32) -> i32:\n    return a + b\n",
        )
        .expect("write source");
        let output_file = NamedTempFile::new().expect("temp vhdl");

        let mut pipeline = CompilerPipeline::new().expect("compiler pipeline");
        pipeline
            .compile_file_to_vhdl(source_file.path(), output_file.path())
            .expect("compile VHDL");

        let vhdl = std::fs::read_to_string(output_file.path()).expect("read VHDL");
        assert!(
            vhdl.starts_with("library ieee;"),
            "expected VHDL library header:\n{vhdl}"
        );
        assert!(vhdl.contains("entity add is"), "expected add entity:\n{vhdl}");
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn compiler_generated_ptx_can_load_and_launch_noop_kernel() {
        let Ok(device_count) = simple_runtime::cuda_runtime::get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let source_file = NamedTempFile::new().expect("temp source");
        std::fs::write(source_file.path(), "@gpu_kernel\nfn noop():\n    pass_dn\n").expect("write temp source");
        let output_file = NamedTempFile::new().expect("temp ptx");

        let mut pipeline = CompilerPipeline::new().expect("compiler pipeline");
        pipeline
            .compile_file_to_ptx(source_file.path(), output_file.path())
            .expect("compile PTX");

        let ptx = std::fs::read_to_string(output_file.path()).expect("read PTX output");
        assert!(ptx.contains(".visible .entry noop("), "expected noop entry PTX:\n{ptx}");

        let ptx_cstr = CString::new(ptx).expect("ptx cstring");
        let kernel_name = CString::new("noop").expect("kernel name");

        let module = simple_runtime::cuda_runtime::rt_cuda_module_load_data(ptx_cstr.as_ptr());
        assert!(module > 0, "expected generated PTX module to load, got {module}");

        let launch =
            simple_runtime::cuda_runtime::rt_cuda_launch_kernel(module, kernel_name.as_ptr(), 1, 1, 1, 1, 1, 1, 0);
        assert_eq!(launch, 0, "expected generated noop kernel to launch, got {launch}");

        let sync = simple_runtime::cuda_runtime::rt_cuda_sync();
        assert_eq!(
            sync, 0,
            "expected sync after generated noop kernel to succeed, got {sync}"
        );

        let unload = simple_runtime::cuda_runtime::rt_cuda_module_unload(module);
        assert_eq!(unload, 0, "expected generated PTX module to unload, got {unload}");
    }
}

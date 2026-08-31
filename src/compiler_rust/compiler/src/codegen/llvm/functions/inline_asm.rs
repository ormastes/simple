//! Operand-bound inline asm and the `@volatile` / `@no_reorder` memory-order
//! helpers for the LLVM backend.
//!
//! Design: `doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md` A.2 (the
//! `@volatile` / `@no_reorder` rows) and A.7 F1/F2 (CSR + barrier intrinsics
//! lower "directly to the existing MIR InlineAsm node with is_volatile=true").

use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;
use crate::hir::TypeId;
use crate::mir::VReg;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
#[cfg(feature = "llvm")]
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum};
#[cfg(feature = "llvm")]
use inkwell::InlineAsmDialect;

/// Bit in `mem_order_mode`: every Load/Store is emitted `volatile`.
pub(crate) const MEM_ORDER_VOLATILE: u8 = 1;
/// Bit in `mem_order_mode`: a single-thread seq_cst fence follows every
/// Load/Store and inline-asm call (compiler barrier, no hardware fence).
pub(crate) const MEM_ORDER_NO_REORDER: u8 = 2;

/// Derive the memory-order mode from a function's attribute list.
pub(crate) fn mem_order_mode_for(attrs: &[String]) -> u8 {
    let mut mode = 0;
    if attrs.iter().any(|a| a == "volatile") {
        mode |= MEM_ORDER_VOLATILE;
    }
    if attrs.iter().any(|a| a == "no_reorder") {
        // `@no_reorder` implies the accesses themselves are volatile — a fence
        // around an access the optimiser may delete protects nothing.
        mode |= MEM_ORDER_NO_REORDER | MEM_ORDER_VOLATILE;
    }
    mode
}

impl LlvmBackend {
    /// Emit one `asm sideeffect` call. Outputs come back as a scalar (one
    /// output) or an anonymous struct (several), then are split into the
    /// output vregs so the MIR `Store`s that follow can write them to their
    /// places.
    #[cfg(feature = "llvm")]
    #[allow(clippy::too_many_arguments)]
    pub(in crate::codegen::llvm) fn compile_inline_asm(
        &self,
        instructions: &[String],
        volatile: bool,
        constraints: &str,
        inputs: &[VReg],
        outputs: &[(VReg, TypeId)],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let ctx = self.context_ref();
        let mut param_types: Vec<BasicMetadataTypeEnum<'static>> = Vec::with_capacity(inputs.len());
        let mut args: Vec<BasicMetadataValueEnum<'static>> = Vec::with_capacity(inputs.len());
        for input in inputs {
            let v = self.get_vreg(input, vreg_map)?;
            param_types.push(v.get_type().into());
            args.push(v.into());
        }
        let out_types: Vec<BasicTypeEnum<'static>> = outputs
            .iter()
            .map(|(_, ty)| self.llvm_type(ty))
            .collect::<Result<_, _>>()?;
        let fn_type = match out_types.len() {
            0 => ctx.void_type().fn_type(&param_types, false),
            1 => out_types[0].fn_type(&param_types, false),
            _ => ctx.struct_type(&out_types, false).fn_type(&param_types, false),
        };
        let asm = ctx.create_inline_asm(
            fn_type,
            instructions.join("\n"),
            constraints.to_string(),
            volatile,
            false,
            Some(InlineAsmDialect::ATT),
            false,
        );
        let call = builder
            .build_indirect_call(fn_type, asm, &args, "")
            .map_err(|e| crate::error::factory::llvm_build_failed("inline_asm", &e))?;
        if outputs.is_empty() {
            return Ok(());
        }
        let Some(ret) = call.try_as_basic_value().left() else {
            return Err(crate::error::factory::llvm_build_failed(
                "inline_asm",
                "asm with outputs returned no value",
            ));
        };
        if outputs.len() == 1 {
            vreg_map.insert(outputs[0].0, ret);
            return Ok(());
        }
        let BasicValueEnum::StructValue(sv) = ret else {
            return Err(crate::error::factory::llvm_build_failed(
                "inline_asm",
                "multi-output asm did not return a struct",
            ));
        };
        for (i, (vreg, _)) in outputs.iter().enumerate() {
            let field = builder
                .build_extract_value(sv, i as u32, "asm_out")
                .map_err(|e| crate::error::factory::llvm_build_failed("inline_asm_extract", &e))?;
            vreg_map.insert(*vreg, field);
        }
        Ok(())
    }

    /// `@no_reorder`: a single-thread seq_cst fence, which is a pure compiler
    /// barrier (no instruction on any target) — hardware ordering is the job
    /// of the `fence()` / `dmb()` intrinsics.
    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn emit_no_reorder_fence(
        &self,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        if self.mem_order_mode.get() & MEM_ORDER_NO_REORDER == 0 {
            return Ok(());
        }
        let single_thread = self.context_ref().get_kind_id("singlethread");
        builder
            .build_fence(
                inkwell::AtomicOrdering::SequentiallyConsistent,
                single_thread as i32,
                "",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("no_reorder_fence", &e))?;
        Ok(())
    }

    /// Whether Load/Store in the current function must be `volatile`.
    pub(in crate::codegen::llvm) fn mem_access_is_volatile(&self) -> bool {
        self.mem_order_mode.get() & MEM_ORDER_VOLATILE != 0
    }
}

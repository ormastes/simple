//! Literal expression lowering: Integer, Float, Bool, String, Nil, ContractResult.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_integer_expr(&mut self, n: i64) -> MirLowerResult<VReg> {
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstInt { dest, value: n });
            dest
        })
    }

    /// Lower an integer literal, keeping a `u64` literal at or above 2^63
    /// visibly unsigned to the backends.
    ///
    /// `ConstInt` carries no type and every backend types it `i64`, so the
    /// bit pattern of `0xFFFF_FFFF_FFFF_FFF8u64` reached `icmp`/`sdiv`/`sshr`
    /// as a negative signed value. A zero-cost `Cast` to `U64` after the
    /// constant gives the vreg its static type. Literals below 2^63 have the
    /// same value under either signedness and stay a bare `ConstInt`, so
    /// constant-pattern consumers (immediates, constant indexes) are
    /// unaffected. Bug: doc/08_tracking/bug/seed_u64_signed_compare_and_u8_data_ptr_2026-10-19.md
    pub(super) fn lower_typed_integer_expr(&mut self, n: i64, ty: TypeId) -> MirLowerResult<VReg> {
        let raw = self.lower_integer_expr(n)?;
        if ty != TypeId::U64 || n >= 0 {
            return Ok(raw);
        }
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Cast {
                dest,
                source: raw,
                from_ty: TypeId::I64,
                to_ty: TypeId::U64,
            });
            dest
        })
    }

    pub(super) fn lower_float_expr(&mut self, f: f64) -> MirLowerResult<VReg> {
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstFloat { dest, value: f });
            dest
        })
    }

    pub(super) fn lower_bool_expr(&mut self, b: bool) -> MirLowerResult<VReg> {
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstBool { dest, value: b });
            dest
        })
    }

    pub(super) fn lower_string_expr(&mut self, s: String) -> MirLowerResult<VReg> {
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstString { dest, value: s });
            dest
        })
    }

    pub(super) fn lower_nil_expr(&mut self) -> MirLowerResult<VReg> {
        // Nil is tagged value 3 in the runtime (TAG_SPECIAL=0b011 | SPECIAL_NIL=0).
        // Must match the runtime's RuntimeValue::NIL representation.
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstInt { dest, value: 3 });
            dest
        })
    }

    pub(super) fn lower_contract_result_expr(&mut self) -> MirLowerResult<VReg> {
        // Return the stored return value from contract context
        let return_value = self.try_contract_ctx()?.return_value;
        if let Some(vreg) = return_value {
            Ok(vreg)
        } else {
            // If no return value is set, create a dummy value (shouldn't happen in valid code)
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                dest
            })
        }
    }
}

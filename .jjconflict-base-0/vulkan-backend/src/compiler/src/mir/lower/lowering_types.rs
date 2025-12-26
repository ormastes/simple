//! Type-related utility methods for MIR lowering
//!
//! This module contains methods for type coercion, union wrapping,
//! and unit type bound checking.

use super::lowering_core::{MirLowerer, MirLowerResult};
use crate::hir::{HirType, TypeId};
use crate::mir::instructions::{MirInst, UnitOverflowBehavior, VReg};

impl<'a> MirLowerer<'a> {
    /// Emit UnionWrap instruction if coercing a value to a Union type
    /// Returns the wrapped value register (or original if no wrapping needed)
    pub(super) fn emit_union_wrap_if_needed(
        &mut self,
        target_ty: TypeId,
        value_ty: TypeId,
        value: VReg,
    ) -> MirLowerResult<VReg> {
        if let Some(registry) = self.type_registry {
            if let Some(HirType::Union { variants }) = registry.get(target_ty) {
                // Check if value_ty is one of the union variants
                if let Some(type_index) = variants.iter().position(|&v| v == value_ty) {
                    // Emit UnionWrap instruction
                    let dest = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::UnionWrap {
                            dest,
                            value,
                            type_index,
                        });
                        dest
                    })?;
                    return Ok(dest);
                }
            }
        }
        Ok(value)
    }

    /// Emit UnitBoundCheck instruction if the type is a UnitType with constraints
    pub(super) fn emit_unit_bound_check(&mut self, ty: TypeId, value: VReg) -> MirLowerResult<()> {
        // Look up type info from registry
        if let Some(registry) = self.type_registry {
            if let Some(hir_type) = registry.get(ty) {
                if let HirType::UnitType {
                    name,
                    constraints,
                    ..
                } = hir_type
                {
                    // Only emit check if there's a range constraint
                    if let Some((min, max)) = constraints.range {
                        let overflow: UnitOverflowBehavior = constraints.overflow.into();
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::UnitBoundCheck {
                                value,
                                unit_name: name.clone(),
                                min,
                                max,
                                overflow,
                            });
                        })?;
                    }
                }
            }
        }
        Ok(())
    }
}

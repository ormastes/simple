//! Identifier expression lowering: Local variable loads and Global variable/enum loads.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirExprKind, HirType, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_local_expr(&mut self, idx: usize, expr_ty: TypeId) -> MirLowerResult<VReg> {
        let is_tagged_local = self.tagged_locals.contains(&idx);
        let result = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let addr_reg = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr_reg,
                local_index: idx,
            });
            block.instructions.push(MirInst::Load {
                dest,
                addr: addr_reg,
                ty: expr_ty,
            });
            dest
        })?;
        // Propagate tagged status from local to loaded VReg
        if is_tagged_local {
            self.tagged_vregs.insert(result);
        }
        Ok(result)
    }

    pub(super) fn lower_global_expr(&mut self, name: String, expr_ty: TypeId) -> MirLowerResult<VReg> {
        // Check if this is an enum variant (contains ::, ., or sanitized _dot_)
        if let Some((enum_name, variant)) = Self::split_enum_qualified_name(&name) {
            // Sanitized enum names from older frontend paths can lose exact variant metadata here.
            let variant_exists = self.is_known_enum_type_for_variant(enum_name, expr_ty);

            // `::` is the enum-variant separator at this IR boundary: static-method
            // refs arrive dot-separated (e.g. `Point.origin`) and fall through below.
            // In a large cross-module unit the type registry can lose an enum's
            // metadata, leaving variant_exists false for a real variant (e.g.
            // `Effect::Compute` when lowering the whole compiler driver). Emit
            // EnumUnit by name anyway — same RuntimeEnum-by-name path the ANY-typed
            // branch already relies on — rather than failing the build.
            // Sibling guard to the one in `lowering_expr_call.rs` (`E.no_such()`):
            // when the head POSITIVELY resolves to a concrete enum and the tail is
            // POSITIVELY not one of its declared variants, do not fabricate an
            // EnumUnit. `EnumUnit` does not consult the variant list, so
            // `Color.Nope` used to lower to an enum-shaped value whose
            // discriminant is a hash of the undeclared name — matching no `case`
            // arm, reported as no error at all, while the interpreter correctly
            // rejects the same program with `unknown variant or method`.
            // `enum_declares_variant` returns `None` whenever the head does not
            // positively resolve to a concrete enum, so the metadata-loss case
            // described below (registry lost `Effect`) stays permissive.
            if self.enum_declares_variant(enum_name, variant, expr_ty) == Some(false)
                && !self.global_types.contains_key(name.as_str())
                && !self.available_functions.contains(name.as_str())
            {
                return Err(MirLowerError::Unsupported(format!(
                    "unknown variant or method '{}' on enum {}{}",
                    variant,
                    enum_name,
                    self.declared_variants_hint(enum_name, expr_ty)
                )));
            }

            if variant_exists || expr_ty == TypeId::ANY || name.contains("::") {
                // Emit EnumUnit instruction for proper RuntimeEnum creation
                let discriminant = self.owned_variant_discriminant(enum_name, variant, expr_ty);
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::EnumUnit {
                        dest,
                        enum_name: enum_name.to_string(),
                        variant_name: variant.to_string(),
                        discriminant,
                    });
                    dest
                });
            }
            // Dot-separated name that's not a known enum — static method reference
            // (e.g. Point.origin). Fall through to GlobalLoad below.
        }

        // Implicit receiver field read: a bare field name inside a class
        // method (`kind` meaning `self.kind`) arrives here as an unresolved
        // `Global` — HIR lowering's lenient branch emits `Global(name)` typed
        // ANY for it. The pure-Simple HIR lane resolves the same idiom to the
        // receiver's field
        // (doc/08_tracking/bug/implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03.md);
        // mirror that here so the MIR lanes (JIT, LLVM, MIR interpreter)
        // compile it instead of dying on an unresolved GlobalLoad.
        if let Some(reg) = self.lower_implicit_receiver_field(&name)? {
            return Ok(reg);
        }

        // Regular global variable - load via GlobalLoad instruction
        let ty = expr_ty; // Use the expression's type
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::GlobalLoad {
                dest,
                global_name: name,
                ty,
            });
            dest
        })
    }

    /// Lower a bare receiver field read (`kind` meaning `self.kind`) when the
    /// current function is a class method whose receiver declares `name` as a
    /// field. Returns `Ok(None)` whenever the situation does not apply (free
    /// function, no receiver, unknown receiver type, or `name` is a known
    /// global/function/import — those keep the `GlobalLoad` path).
    ///
    /// The read is delegated to the ordinary field-access lowering via a
    /// synthetic, CONCRETELY typed `self.<field>` expression. Typing matters:
    /// the unresolved `Global` arrives typed ANY, and ANY-typed operands take
    /// runtime tag-dispatched paths (`rt_any_add`, boxed equality) that
    /// misinterpret the raw field word. Re-typing the read to the field's
    /// declared type reproduces exactly what an explicit `self.<field>`
    /// spelling lowers to — the semantics the pure-Simple lane implements.
    fn lower_implicit_receiver_field(&mut self, name: &str) -> MirLowerResult<Option<VReg>> {
        // A name that positively resolves to a module-level symbol stays a
        // global reference; only genuinely unresolved names fall through to
        // the receiver field. Same guard population as the enum-variant
        // sibling above, plus function-value globals and imported names.
        if self.global_types.contains_key(name)
            || self.available_functions.contains(name)
            || self.function_value_globals.contains(name)
            || self.imported_function_names.contains(name)
        {
            return Ok(None);
        }
        let Some(registry) = self.type_registry else {
            return Ok(None);
        };
        // The receiver is param local 0 whenever HIR lowering put `self` in
        // scope (explicit parser-injected parameter or the implicit one added
        // for plain `fn` class methods).
        let receiver = self.with_func(|func, _| {
            let param = func.params.first()?;
            (param.name == "self" || param.name == "me").then(|| (0_usize, param.ty))
        })?;
        let Some((receiver_index, receiver_ty)) = receiver else {
            return Ok(None);
        };
        let mut ty = registry.get(receiver_ty);
        if let Some(HirType::Pointer { inner, .. }) = ty {
            // Classes are commonly pointer-wrapped at the MIR boundary;
            // follow one layer exactly like TypeRegistry::get_type_name.
            if *inner != receiver_ty {
                ty = registry.get(*inner);
            }
        }
        let Some(HirType::Struct { fields, .. }) = ty else {
            return Ok(None);
        };
        let Some(field_index) = fields.iter().position(|(field, _)| field == name) else {
            return Ok(None);
        };
        let field_type = fields[field_index].1;
        let synthetic = HirExpr {
            kind: HirExprKind::FieldAccess {
                receiver: Box::new(HirExpr {
                    kind: HirExprKind::Local(receiver_index),
                    ty: receiver_ty,
                }),
                field_index,
            },
            ty: field_type,
        };
        self.lower_expr(&synthetic).map(Some)
    }
}
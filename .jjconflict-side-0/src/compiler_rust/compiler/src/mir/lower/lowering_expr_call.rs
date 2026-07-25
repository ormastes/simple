//! Direct and indirect function call expression lowering.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{DispatchMode, HirExpr, HirExprKind, HirType, TypeId};
use crate::method_registry::GLOBAL_REGISTRY;
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn split_enum_qualified_name<'b>(name: &'b str) -> Option<(&'b str, &'b str)> {
        name.split_once("::")
            .or_else(|| name.split_once('.'))
            .or_else(|| name.split_once("_dot_"))
    }

    pub(super) fn is_known_enum_type_for_variant(&self, enum_name: &str, fallback_ty: TypeId) -> bool {
        if let Some(registry) = self.type_registry {
            if let Some(type_id) = registry.lookup(enum_name) {
                return matches!(registry.get(type_id), Some(crate::hir::HirType::Enum { .. }));
            }
            return matches!(registry.get(fallback_ty), Some(crate::hir::HirType::Enum { .. }));
        }
        false
    }

    fn enum_payload_type_for_call_receiver(&self, ty: TypeId) -> Option<TypeId> {
        let registry = self.type_registry?;
        match registry.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants
                .iter()
                .find_map(|(_, payload)| payload.as_ref().and_then(|fields| fields.first()).copied()),
            Some(HirType::Pointer { inner, .. }) if *inner != ty => self.enum_payload_type_for_call_receiver(*inner),
            _ => None,
        }
    }

    fn enum_variant_payload_type_for_call_receiver(&self, ty: TypeId, variant_name: &str) -> Option<TypeId> {
        let registry = self.type_registry?;
        match registry.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants.iter().find_map(|(name, payload)| {
                if name == variant_name {
                    payload.as_ref().and_then(|fields| fields.first()).copied()
                } else {
                    None
                }
            }),
            Some(HirType::Pointer { inner, .. }) if *inner != ty => {
                self.enum_variant_payload_type_for_call_receiver(*inner, variant_name)
            }
            _ => None,
        }
    }

    fn function_signature_for_callee(&self, callee: &HirExpr, arg_count: usize) -> (Vec<TypeId>, TypeId) {
        let Some(registry) = self.type_registry else {
            return (vec![TypeId::ANY; arg_count], TypeId::ANY);
        };
        if let Some(HirType::Function { params, ret }) = registry.get(callee.ty) {
            return (params.clone(), *ret);
        }
        if let HirExprKind::Index { receiver, .. } = &callee.kind {
            if let Some(HirType::Array { element, .. }) = registry.get(receiver.ty) {
                if let Some(HirType::Function { params, ret }) = registry.get(*element) {
                    return (params.clone(), *ret);
                }
            }
        }
        (vec![TypeId::ANY; arg_count], TypeId::ANY)
    }

    fn call_returns_array_of(&self, callee: &HirExpr, element_type: TypeId) -> bool {
        let Some(registry) = self.type_registry else {
            return false;
        };
        if matches!(registry.get(callee.ty), Some(HirType::Array { element, .. }) if *element == element_type) {
            return true;
        }
        let Some(HirType::Function { ret, .. }) = registry.get(callee.ty) else {
            return false;
        };
        matches!(registry.get(*ret), Some(HirType::Array { element, .. }) if *element == element_type)
    }

    /// Box a scalar payload value before storing it in an `Option`/`Result`
    /// enum object (`OptionSome`/`ResultOk`/`ResultErr`).
    ///
    /// `rt_enum_new` stores `payload` as an opaque `RuntimeValue` and
    /// `rt_enum_payload`/`rt_unwrap_or_self` return it verbatim — the
    /// convention everywhere else in this runtime is that such payloads are
    /// tagged (`(value << 3) | TAG_INT` for ints, `TAG_HEAP` for heap
    /// objects). Integer/bool literals lowered as MIR values are native
    /// (untagged) scalars, so storing them directly makes the enum's
    /// payload field hold a raw value with an accidental tag-bit pattern:
    /// `Some(9)` stores raw `9`, whose low 3 bits (`0b001`) happen to equal
    /// `TAG_HEAP`, so a later consumer (e.g. `print`) misreads it as an
    /// invalid heap pointer (`<invalid-heap:0x9>`) instead of the tagged int
    /// `9`. This mirrors the general enum-variant-payload boxing already
    /// done a few lines below for arbitrary user enums (see
    /// `doc/08_tracking/bug/enum_field_i64_zero_destructure_2026-04-28.md`);
    /// the `Some`/`Ok`/`Err` fast paths above bypassed that logic.
    fn box_enum_payload_if_needed(&mut self, value: VReg, arg_ty: TypeId) -> MirLowerResult<VReg> {
        let needs_box = matches!(
            arg_ty,
            TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
                | TypeId::BOOL
        );
        if !needs_box {
            return Ok(value);
        }
        self.with_func(|func, current_block| {
            let boxed = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::BoxInt { dest: boxed, value });
            boxed
        })
    }

    pub(super) fn box_arg_for_any_param(&mut self, arg: VReg, arg_expr: &HirExpr) -> MirLowerResult<VReg> {
        let arg_ty = arg_expr.ty;
        let needs_int_box = matches!(
            arg_ty,
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
        ) || (arg_ty == TypeId::ANY && matches!(arg_expr.kind, HirExprKind::Integer(_)));
        if needs_int_box {
            self.with_func(|func, current_block| {
                let boxed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BoxInt {
                    dest: boxed,
                    value: arg,
                });
                boxed
            })
        } else if matches!(arg_ty, TypeId::F32 | TypeId::F64)
            || (arg_ty == TypeId::ANY && matches!(arg_expr.kind, HirExprKind::Float(_)))
        {
            self.with_func(|func, current_block| {
                let boxed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BoxFloat {
                    dest: boxed,
                    value: arg,
                });
                boxed
            })
        } else {
            Ok(arg)
        }
    }

    pub(super) fn box_args_for_any_params(
        &mut self,
        callee: &HirExpr,
        args: &[HirExpr],
        arg_regs: &mut [VReg],
    ) -> MirLowerResult<()> {
        let params = if let Some(registry) = self.type_registry {
            if let Some(HirType::Function { params, .. }) = registry.get(callee.ty) {
                params.clone()
            } else if let HirExprKind::Global(name) = &callee.kind {
                self.function_param_types.get(name).cloned().unwrap_or_default()
            } else {
                Vec::new()
            }
        } else if let HirExprKind::Global(name) = &callee.kind {
            self.function_param_types.get(name).cloned().unwrap_or_default()
        } else {
            Vec::new()
        };
        if params.is_empty() {
            return Ok(());
        }
        for (i, arg_reg) in arg_regs.iter_mut().enumerate() {
            if params.get(i).copied() == Some(TypeId::ANY) {
                if let Some(arg_expr) = args.get(i) {
                    *arg_reg = self.box_arg_for_any_param(*arg_reg, arg_expr)?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn lower_call_expr(&mut self, callee: &HirExpr, args: &[HirExpr]) -> MirLowerResult<VReg> {
        if let HirExprKind::Global(name) = &callee.kind {
            if let Some((receiver_name, method_name)) = name.rsplit_once('.') {
                if matches!(method_name, "push" | "append" | "len") {
                    if let Some(receiver_ty) = self.global_types.get(receiver_name).copied() {
                        if self
                            .type_registry
                            .and_then(|registry| registry.get(receiver_ty))
                            .is_some_and(|ty| matches!(ty, HirType::Array { .. }))
                        {
                            let receiver_expr = HirExpr {
                                kind: HirExprKind::Global(receiver_name.to_string()),
                                ty: receiver_ty,
                            };
                            return self.lower_method_call_expr(
                                &receiver_expr,
                                method_name,
                                args,
                                &DispatchMode::Dynamic,
                            );
                        }
                    }
                }
            }
        }

        if let HirExprKind::Global(name) = &callee.kind {
            // Standard-library trait defaults may arrive as module-mangled global
            // aliases. Re-enter normal concrete method lowering when the receiver
            // is a builtin type; leave all other aliases on the ordinary path.
            if let Some((_, method)) = GLOBAL_REGISTRY.compatibility_alias(name) {
                if let Some(receiver) = args.first() {
                    let receiver_ty = self.recover_receiver_type(receiver).unwrap_or(receiver.ty);
                    let receiver_type = self
                        .type_registry
                        .and_then(|registry| registry.get(receiver_ty))
                        .and_then(|ty| match ty {
                            HirType::Array { .. } => Some("Array"),
                            HirType::Dict { .. } => Some("Dict"),
                            HirType::Tuple(_) | HirType::LabeledTuple(_) => Some("Tuple"),
                            HirType::String => Some("String"),
                            HirType::Struct { name, .. } if name == "String" || name == "text" || name == "str" => {
                                Some("String")
                            }
                            _ => None,
                        });
                    if receiver_type.is_some_and(|type_name| GLOBAL_REGISTRY.has_method(type_name, method)) {
                        return self.lower_method_call_expr(receiver, method, &args[1..], &DispatchMode::Static);
                    }
                }
            }
        }

        let mut arg_regs = Vec::new();
        for arg in args {
            arg_regs.push(self.lower_expr(arg)?);
        }

        // Direct call or indirect call?
        if let HirExprKind::Global(name) = &callee.kind {
            match (name.as_str(), arg_regs.as_slice()) {
                ("Some", [value]) => {
                    let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                    let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::OptionSome { dest, value });
                        dest
                    });
                }
                ("Ok", [value]) => {
                    let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                    let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ResultOk { dest, value });
                        dest
                    });
                }
                ("Err", [value]) => {
                    let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                    let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ResultErr { dest, value });
                        dest
                    });
                }
                ("None", []) => {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::OptionNone { dest });
                        dest
                    });
                }
                _ => {}
            }

            if self.function_value_globals.contains(name) {
                self.box_args_for_any_params(callee, args, &mut arg_regs)?;
                let callee_reg = self.lower_global_expr(name.clone(), callee.ty)?;
                let (param_types, return_type) = self.function_signature_for_callee(callee, arg_regs.len());
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::IndirectCall {
                        dest: Some(dest),
                        callee: callee_reg,
                        param_types,
                        return_type,
                        args: arg_regs,
                        effect: crate::mir::effects::Effect::Io,
                    });
                    dest
                });
            }

            // Check if this is an enum variant constructor (e.g., "Color::Blue" or "Color.Blue")
            if let Some((enum_name, variant_name)) = Self::split_enum_qualified_name(name) {
                if arg_regs.len() == 1 {
                    let receiver = args.first();
                    match variant_name {
                        "unwrap" => {
                            let payload_ty = receiver
                                .and_then(|arg| self.enum_payload_type_for_call_receiver(arg.ty))
                                .or_else(|| {
                                    self.type_registry
                                        .and_then(|registry| registry.lookup(enum_name))
                                        .and_then(|ty| self.enum_payload_type_for_call_receiver(ty))
                                });
                            if let (Some(payload_ty), Some(receiver)) = (payload_ty, receiver) {
                                return self.lower_builtin_call_expr(
                                    "rt_enum_payload",
                                    std::slice::from_ref(receiver),
                                    payload_ty,
                                );
                            }
                        }
                        "unwrap_err" => {
                            let payload_ty = receiver
                                .and_then(|arg| self.enum_variant_payload_type_for_call_receiver(arg.ty, "Err"))
                                .or_else(|| {
                                    self.type_registry
                                        .and_then(|registry| registry.lookup(enum_name))
                                        .and_then(|ty| self.enum_variant_payload_type_for_call_receiver(ty, "Err"))
                                });
                            if let (Some(payload_ty), Some(receiver)) = (payload_ty, receiver) {
                                return self.lower_builtin_call_expr(
                                    "rt_enum_payload",
                                    std::slice::from_ref(receiver),
                                    payload_ty,
                                );
                            }
                        }
                        "is_ok" | "is_err" => {
                            if let Some(receiver) = receiver {
                                let expected = HirExpr {
                                    kind: HirExprKind::Integer(Self::enum_variant_discriminant(
                                        if variant_name == "is_ok" { "Ok" } else { "Err" },
                                    )),
                                    ty: TypeId::I64,
                                };
                                let builtin_args = [receiver.clone(), expected];
                                return self.lower_builtin_call_expr(
                                    "rt_enum_check_discriminant",
                                    &builtin_args,
                                    TypeId::BOOL,
                                );
                            }
                        }
                        _ => {}
                    }
                }

                match (enum_name, variant_name, arg_regs.as_slice()) {
                    ("Option", "Some", [value]) => {
                        let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                        let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::OptionSome { dest, value });
                            dest
                        });
                    }
                    ("Option", "None", []) => {
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::OptionNone { dest });
                            dest
                        });
                    }
                    ("Result", "Ok", [value]) => {
                        let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                        let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ResultOk { dest, value });
                            dest
                        });
                    }
                    ("Result", "Err", [value]) => {
                        let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                        let value = self.box_enum_payload_if_needed(*value, arg_ty)?;
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ResultErr { dest, value });
                            dest
                        });
                    }
                    _ => {}
                }

                // Check if this is an enum type via the type registry or callee type
                let is_enum = self.is_known_enum_type_for_variant(enum_name, callee.ty);

                if is_enum && !arg_regs.is_empty() {
                    // Single-arg variants store the argument directly as the
                    // enum payload. Primitive payloads still need runtime
                    // boxing, the same as multi-arg payload array entries.
                    let payload_reg = if arg_regs.len() == 1 {
                        let arg_ty = args.first().map(|a| a.ty).unwrap_or(TypeId::ANY);
                        let needs_box = matches!(
                            arg_ty,
                            TypeId::I8
                                | TypeId::I16
                                | TypeId::I32
                                | TypeId::I64
                                | TypeId::U8
                                | TypeId::U16
                                | TypeId::U32
                                | TypeId::U64
                                | TypeId::BOOL
                        );
                        if needs_box {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxInt {
                                    dest: boxed,
                                    value: arg_regs[0],
                                });
                                boxed
                            })?
                        } else {
                            arg_regs[0]
                        }
                    } else {
                        // Create an array with all args as the payload
                        let array_reg = self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: Some(dest),
                                target: CallTarget::from_name("rt_array_new"),
                                args: vec![],
                            });
                            dest
                        })?;
                        // Push each arg into the array. `rt_array_push` (per its
                        // runtime comment) expects values to arrive *tagged*; for
                        // integer-typed args we must insert MirInst::BoxInt first,
                        // mirroring what regular `arr.push(int)` lowering does.
                        // Without this, integer enum fields are stored untagged,
                        // and destructuring later applies DECODE_INT to a raw int,
                        // silently zeroing the field. See
                        // doc/08_tracking/bug/enum_field_i64_zero_destructure_2026-04-28.md.
                        for (i, arg) in arg_regs.iter().enumerate() {
                            let arg_ty = args.get(i).map(|a| a.ty).unwrap_or(TypeId::ANY);
                            let needs_box = matches!(
                                arg_ty,
                                TypeId::I8
                                    | TypeId::I16
                                    | TypeId::I32
                                    | TypeId::I64
                                    | TypeId::U8
                                    | TypeId::U16
                                    | TypeId::U32
                                    | TypeId::U64
                                    | TypeId::BOOL
                            );
                            // Float payloads need BoxFloat (lossless heap box):
                            // a raw double stored untagged loses its low 3
                            // mantissa bits to tag decoding on extraction —
                            // f64 enum payloads read back 0.09999999999999998.
                            // Mirrors the arr.push(float) fix in
                            // lowering_expr_method.rs; see
                            // doc/08_tracking/bug/seed_f64_array_element_precision_mask_2026-07-19.md.
                            let needs_float_box = matches!(arg_ty, TypeId::F32 | TypeId::F64);
                            let push_arg = if needs_box || needs_float_box {
                                self.with_func(|func, current_block| {
                                    let boxed = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    if needs_float_box {
                                        block.instructions.push(MirInst::BoxFloat {
                                            dest: boxed,
                                            value: *arg,
                                        });
                                    } else {
                                        block.instructions.push(MirInst::BoxInt {
                                            dest: boxed,
                                            value: *arg,
                                        });
                                    }
                                    boxed
                                })?
                            } else {
                                *arg
                            };
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: CallTarget::from_name("rt_array_push"),
                                    args: vec![array_reg, push_arg],
                                });
                            })?;
                        }
                        array_reg
                    };
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::EnumWith {
                            dest,
                            enum_name: enum_name.to_string(),
                            variant_name: variant_name.to_string(),
                            payload: payload_reg,
                        });
                        dest
                    });
                }
                if is_enum {
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::EnumUnit {
                            dest,
                            enum_name: enum_name.to_string(),
                            variant_name: variant_name.to_string(),
                        });
                        dest
                    });
                }
            }

            // Direct call - DI injection is handled at the HIR level
            // The function signature already includes all parameters (including @inject ones)
            // So we don't inject at call sites during MIR lowering
            // NOTE: DI injection at MIR level was causing signature mismatches
            // because functions were registered with all params but calls tried to inject again

            self.box_args_for_any_params(callee, args, &mut arg_regs)?;

            // Colliding private helpers were emitted under mangled names (see
            // `private_dup_overloads`): resolve this call site to the variant
            // whose parameter types exactly match the argument types. No exact
            // match: prefer an extern decl of the same name (the local defs
            // demonstrably have different signatures), else the last local
            // definition — the previous last-write-wins behavior.
            let dup_resolved: Option<String> = self.private_dup_overloads.get(name.as_str()).and_then(|candidates| {
                let arg_tys: Vec<TypeId> = args.iter().map(|a| a.ty).collect();
                let exact = candidates.iter().find(|(param_tys, _)| *param_tys == arg_tys);
                // No exact type match (args may have inferred as Any): if the
                // arity singles out one candidate, that is still unambiguous.
                let by_arity = || {
                    let mut same_arity = candidates
                        .iter()
                        .filter(|(param_tys, _)| param_tys.len() == arg_tys.len());
                    match (same_arity.next(), same_arity.next()) {
                        (Some(only), None) => Some(only),
                        _ => None,
                    }
                };
                exact.or_else(by_arity).map(|(_, mangled)| mangled.clone()).or_else(|| {
                    if self.extern_fn_name_set.contains(name.as_str()) {
                        None // keep bare name → extern import
                    } else {
                        candidates.last().map(|(_, mangled)| mangled.clone())
                    }
                })
            });
            let call_target_name = if let Some(mangled) = dup_resolved.as_deref() {
                mangled
            } else if name == "rt_array_new_with_cap" && self.call_returns_array_of(callee, TypeId::U64) {
                "rt_array_new_with_cap_u64"
            } else {
                name
            };
            let call_target = CallTarget::from_name(call_target_name);
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: call_target,
                    args: arg_regs,
                });
                dest
            })
        } else {
            // Indirect call through closure/function pointer
            let callee_reg = self.lower_expr(callee)?;

            let (param_types, return_type) = self.function_signature_for_callee(callee, arg_regs.len());

            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::IndirectCall {
                    dest: Some(dest),
                    callee: callee_reg,
                    param_types,
                    return_type,
                    args: arg_regs,
                    effect: crate::mir::effects::Effect::Io,
                });
                dest
            })
        }
    }
}

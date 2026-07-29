//! Method call expression lowering (static and dynamic dispatch).

use super::lowering_core::{MirLowerResult, MirLowerer};
use super::lowering_di::builtin_type_name;
use crate::hir::{DispatchMode, HirExpr, HirType, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    fn box_method_args_for_any_params(
        &mut self,
        func_name: &str,
        args: &[HirExpr],
        arg_regs: &mut [VReg],
    ) -> MirLowerResult<()> {
        let params = self.function_param_types.get(func_name).cloned().unwrap_or_default();
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

    fn builtin_method_receiver_name(&self, ty: TypeId) -> Option<&'static str> {
        if let Some(name) = builtin_type_name(ty) {
            return Some(name);
        }
        let registry = self.type_registry?;
        match registry.get(ty) {
            Some(HirType::Array { .. }) => Some("Array"),
            Some(HirType::Dict { .. }) => Some("Dict"),
            Some(HirType::Tuple(_) | HirType::LabeledTuple(_)) => Some("Tuple"),
            _ => None,
        }
    }

    fn receiver_is_array(&self, receiver: &HirExpr, recovered_ty: Option<TypeId>) -> bool {
        let Some(registry) = self.type_registry else {
            return false;
        };
        matches!(registry.get(receiver.ty), Some(HirType::Array { .. }))
            || recovered_ty.is_some_and(|ty| matches!(registry.get(ty), Some(HirType::Array { .. })))
    }

    /// Same shape as `receiver_is_array`, for `Dict<K, V>` receivers. Used to
    /// route `d.get(k)` through `lower_index_expr` — see the call site below
    /// (task: dict_value_read_returns_tag_boxed_word).
    fn receiver_is_dict(&self, receiver: &HirExpr, recovered_ty: Option<TypeId>) -> bool {
        let Some(registry) = self.type_registry else {
            return false;
        };
        matches!(registry.get(receiver.ty), Some(HirType::Dict { .. }))
            || recovered_ty.is_some_and(|ty| matches!(registry.get(ty), Some(HirType::Dict { .. })))
    }

    fn enum_payload_type_for_method_receiver(&self, ty: TypeId) -> Option<TypeId> {
        let registry = self.type_registry?;
        match registry.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants
                .iter()
                .find_map(|(_, payload)| payload.as_ref().and_then(|fields| fields.first()).copied()),
            Some(HirType::Pointer { inner, .. }) if *inner != ty => self.enum_payload_type_for_method_receiver(*inner),
            _ => None,
        }
    }

    /// True when the receiver's NAMED type is the builtin `Result`/`Option`
    /// enum, even if the generic instantiation's variants are not materialized
    /// in the type registry (e.g. `Result<Value, BackendError>` with imported
    /// payload types). For such receivers the zero-arg enum helpers
    /// (`unwrap`/`unwrap_err`/`is_ok`/`is_err`/`is_some`/`is_none`) are ALWAYS
    /// the builtin enum operations; emitting a name-dispatched
    /// `MethodCallStatic("Result.is_err")` instead lets the codegen name-suffix
    /// fallback rebind them to unrelated user methods whose type name merely
    /// contains "Result" as a substring (`FailSafeResult.is_err`) or to a
    /// last-resort bare import-map entry (`Poll.unwrap`) — the stage4 macOS
    /// interpreter corruption where every interpreted `Value` became 0 and
    /// printed `<unknown>` (2026-07-25).
    fn receiver_is_builtin_result_or_option(&self, ty: TypeId, local_ty: Option<TypeId>) -> bool {
        let Some(registry) = self.type_registry else {
            return false;
        };
        [Some(ty), local_ty]
            .into_iter()
            .flatten()
            .any(|t| matches!(registry.get_type_name(t), Some("Result" | "Option")))
    }

    fn enum_variant_payload_type_for_method_receiver(&self, ty: TypeId, variant_name: &str) -> Option<TypeId> {
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
                self.enum_variant_payload_type_for_method_receiver(*inner, variant_name)
            }
            _ => None,
        }
    }

    fn enum_has_variant_for_method_receiver(&self, ty: TypeId, variant_name: &str) -> bool {
        let registry = match self.type_registry {
            Some(registry) => registry,
            None => return false,
        };
        match registry.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants.iter().any(|(name, _)| name == variant_name),
            Some(HirType::Pointer { inner, .. }) if *inner != ty => {
                self.enum_has_variant_for_method_receiver(*inner, variant_name)
            }
            _ => false,
        }
    }

    pub(super) fn enum_variant_discriminant(variant_name: &str) -> i64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        variant_name.hash(&mut hasher);
        (hasher.finish() & 0xFFFF_FFFF) as i64
    }

    pub(super) fn lower_method_call_expr(
        &mut self,
        receiver: &HirExpr,
        method: &str,
        args: &[HirExpr],
        dispatch: &DispatchMode,
    ) -> MirLowerResult<VReg> {
        let receiver_local_ty: Option<TypeId> = self.recover_receiver_type(receiver);

        if args.is_empty() {
            let effective_ty = receiver_local_ty.unwrap_or(receiver.ty);
            match method {
                "ord" | "codepoint" | "code_point" if effective_ty == TypeId::STRING => {
                    let zero = HirExpr {
                        kind: crate::hir::HirExprKind::Integer(0),
                        ty: TypeId::I64,
                    };
                    let args = [receiver.clone(), zero];
                    return self.lower_builtin_call_expr("rt_string_char_code_at", &args, TypeId::I64);
                }
                "hash" if effective_ty == TypeId::STRING => {
                    return self.lower_builtin_call_expr("rt_str_hash", std::slice::from_ref(receiver), TypeId::I64);
                }
                "unwrap" => {
                    if let Some(payload_ty) = self
                        .enum_payload_type_for_method_receiver(receiver.ty)
                        .or_else(|| self.enum_payload_type_for_method_receiver(effective_ty))
                    {
                        return self.lower_builtin_call_expr(
                            "rt_enum_payload",
                            std::slice::from_ref(receiver),
                            payload_ty,
                        );
                    }
                    if self.receiver_is_builtin_result_or_option(receiver.ty, Some(effective_ty)) {
                        return self.lower_builtin_call_expr(
                            "rt_enum_payload",
                            std::slice::from_ref(receiver),
                            TypeId::ANY,
                        );
                    }
                }
                "unwrap_err" => {
                    if let Some(payload_ty) = self
                        .enum_variant_payload_type_for_method_receiver(receiver.ty, "Err")
                        .or_else(|| self.enum_variant_payload_type_for_method_receiver(effective_ty, "Err"))
                    {
                        return self.lower_builtin_call_expr(
                            "rt_enum_payload",
                            std::slice::from_ref(receiver),
                            payload_ty,
                        );
                    }
                    if self.receiver_is_builtin_result_or_option(receiver.ty, Some(effective_ty)) {
                        return self.lower_builtin_call_expr(
                            "rt_enum_payload",
                            std::slice::from_ref(receiver),
                            TypeId::ANY,
                        );
                    }
                }
                "is_some" => {
                    if self.enum_has_variant_for_method_receiver(receiver.ty, "Some")
                        || self.enum_has_variant_for_method_receiver(effective_ty, "Some")
                        || self.receiver_is_builtin_result_or_option(receiver.ty, Some(effective_ty))
                    {
                        return self.lower_builtin_call_expr(
                            "rt_is_some",
                            std::slice::from_ref(receiver),
                            TypeId::BOOL,
                        );
                    }
                }
                "is_none" => {
                    if self.enum_has_variant_for_method_receiver(receiver.ty, "None")
                        || self.enum_has_variant_for_method_receiver(effective_ty, "None")
                        || self.receiver_is_builtin_result_or_option(receiver.ty, Some(effective_ty))
                    {
                        return self.lower_builtin_call_expr(
                            "rt_is_none",
                            std::slice::from_ref(receiver),
                            TypeId::BOOL,
                        );
                    }
                }
                "is_ok" | "is_err" => {
                    let variant_name = if method == "is_ok" { "Ok" } else { "Err" };
                    if self.enum_has_variant_for_method_receiver(receiver.ty, variant_name)
                        || self.enum_has_variant_for_method_receiver(effective_ty, variant_name)
                        || self.receiver_is_builtin_result_or_option(receiver.ty, Some(effective_ty))
                    {
                        let expected = HirExpr {
                            kind: crate::hir::HirExprKind::Integer(Self::enum_variant_discriminant(variant_name)),
                            ty: TypeId::I64,
                        };
                        let args = [receiver.clone(), expected];
                        return self.lower_builtin_call_expr("rt_enum_check_discriminant", &args, TypeId::BOOL);
                    }
                }
                _ => {}
            }
        }

        // `xs.get(i)` on an array is the SAME read as `xs[i]`, but the generic
        // dotted-name path emitted a bare `rt_index_get` and fed the tag-boxed
        // slot word (`rt_value_int(v) == v << 3`) straight into an int-typed
        // VReg — so every `[i64].get(i)` came back exactly 8x too large,
        // silently, exit 0. `xs[i]` is correct precisely because
        // `lower_index_expr` pairs the read with an explicit
        // `UnboxInt`/`UnboxFloat` (+ `UnitNarrow` for narrow element widths).
        // Route `.get(i)` through that exact path. This sits BEFORE the receiver
        // and args are lowered, so nothing is evaluated twice. Dict/String/tuple
        // receivers are untouched — `receiver_is_array` gates it.
        // See doc/08_tracking/bug/list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md
        if method == "get" && args.len() == 1 && self.receiver_is_array(receiver, receiver_local_ty) {
            let element_ty = self
                .type_registry
                .and_then(|tr| {
                    tr.get(receiver.ty)
                        .or_else(|| receiver_local_ty.and_then(|ty| tr.get(ty)))
                })
                .and_then(|ty| match ty {
                    HirType::Array { element, .. } => Some(*element),
                    _ => None,
                })
                .unwrap_or(TypeId::ANY);
            return self.lower_index_expr(receiver, &args[0], element_ty);
        }

        // `d.get(k)` on a Dict<K, V> is the SAME read as `d[k]`, but the
        // generic dotted-name/dynamic-dispatch path emitted a bare
        // `MethodCallStatic` -> `rt_index_get` with NO UnboxInt on the result
        // at all — `Dict.get` never unboxed. `d[k]` was always correct
        // BECAUSE `lower_index_expr` pairs the read with an explicit
        // `UnboxInt` (tag-aware: only shifts a truly-tagged scalar, Task
        // #123). Route `.get(k)` through that exact path, mirroring the
        // `[T].get(i)` fix above. This must land together with the dict
        // LITERAL now boxing its values on write (lowering_expr_collection.rs
        // `lower_dict_expr`): boxing the value without unboxing `.get()` (or
        // vice versa) breaks the OTHER read path — see the comment there.
        // See task: dict_value_read_returns_tag_boxed_word.
        if method == "get" && args.len() == 1 && self.receiver_is_dict(receiver, receiver_local_ty) {
            let value_ty = self
                .type_registry
                .and_then(|tr| {
                    tr.get(receiver.ty)
                        .or_else(|| receiver_local_ty.and_then(|ty| tr.get(ty)))
                })
                .and_then(|ty| match ty {
                    HirType::Dict { value, .. } => Some(*value),
                    _ => None,
                })
                .unwrap_or(TypeId::ANY);
            return self.lower_index_expr(receiver, &args[0], value_ty);
        }

        // rt_array_push returns bool, not a new pointer — no store-back needed.
        let _receiver_local_index: Option<usize> = None;

        let mut receiver_reg = self.lower_expr(receiver)?;
        let mut arg_regs = Vec::new();
        for arg in args {
            arg_regs.push(self.lower_expr(arg)?);
        }

        // Function-valued struct field invoked with method syntax:
        // `port.run_fn(args)` where `struct BackendPort { run_fn: any }` holds a
        // lambda. Name-based method resolution cannot find a function called
        // "BackendPort.run_fn" and codegen would emit rt_function_not_found at
        // runtime (stage4 phase5:mode_dispatch failure, 2026-06-10). Lower it
        // as FieldGet (sequential i*8 layout, same as lowering_expr_struct) +
        // IndirectCall through the closure value instead.
        if let Some(registry) = self.type_registry {
            let field_hit = [Some(receiver.ty), receiver_local_ty]
                .into_iter()
                .flatten()
                .find_map(|t| match registry.get(t) {
                    Some(HirType::Struct { fields, .. }) => fields
                        .iter()
                        .enumerate()
                        .find(|(_, (n, _))| n == method)
                        .map(|(i, (_, fty))| (t, i, *fty)),
                    _ => None,
                });
            if let Some((owner_ty, field_index, field_ty)) = field_hit {
                let field_signature = match registry.get(field_ty) {
                    Some(HirType::Function { params, ret }) => Some((params.clone(), *ret)),
                    _ => None,
                };
                let is_callable_field = field_ty == TypeId::ANY || field_signature.is_some();
                if is_callable_field {
                    let (param_types, return_type) =
                        field_signature.unwrap_or_else(|| (vec![TypeId::ANY; args.len()], TypeId::ANY));
                    for (i, arg_reg) in arg_regs.iter_mut().enumerate() {
                        if param_types.get(i).copied() == Some(TypeId::ANY) {
                            if let Some(arg_expr) = args.get(i) {
                                *arg_reg = self.box_arg_for_any_param(*arg_reg, arg_expr)?;
                            }
                        }
                    }
                    let owner_name = self
                        .type_registry
                        .and_then(|registry| registry.get_type_name(owner_ty))
                        .map(str::to_owned);
                    // Native-project lowering replaces this with an
                    // authoritative module-qualified layout decision.
                    let owner_has_vtable = None;
                    return self.with_func(|func, current_block| {
                        let fval = func.new_vreg();
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::FieldGet {
                            dest: fval,
                            object: receiver_reg,
                            owner_name,
                            owner_has_vtable,
                            byte_offset: (field_index as u32) * 8,
                            field_type: field_ty,
                        });
                        block.instructions.push(MirInst::IndirectCall {
                            dest: Some(dest),
                            callee: fval,
                            param_types,
                            return_type,
                            args: arg_regs.clone(),
                            effect: crate::mir::effects::Effect::Io,
                        });
                        dest
                    });
                }
            }
        }

        if method == "char_code_at"
            && args.len() == 1
            && (receiver.ty == TypeId::STRING || receiver_local_ty == Some(TypeId::STRING))
        {
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_string_char_code_at"),
                    args: vec![receiver_reg, arg_regs[0]],
                });
                dest
            });
        }

        if method == "len" && args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_len"),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `first` / `last` / `pop` hand back an array SLOT verbatim, and array
        // slots hold tag-boxed values (`rt_value_int(v) == v << 3`). The generic
        // dotted-name path fed that tagged word straight into an int-typed VReg,
        // so on the JIT every `[i64].first()/.last()/.pop()` read exactly 8x too
        // large — silently, exit 0. The `arr[i]` path is correct precisely
        // because IndexGet is always paired with an explicit `UnboxInt` (see
        // `compile_index_get`: codegen deliberately returns the RuntimeValue raw
        // and leaves type-specific unboxing to MIR). Restore that pairing here.
        // Only native scalar element types unbox; text/struct/array elements are
        // already valid RuntimeValue pointers and must pass through untouched.
        if args.is_empty() && matches!(method, "first" | "last" | "pop") {
            let element_ty = self
                .type_registry
                .and_then(|tr| {
                    tr.get(receiver.ty)
                        .or_else(|| receiver_local_ty.and_then(|ty| tr.get(ty)))
                })
                .and_then(|ty| match ty {
                    HirType::Array { element, .. } => Some(*element),
                    _ => None,
                });
            if let Some(element_ty) = element_ty {
                let rt_name = match method {
                    "first" => "rt_array_first",
                    "last" => "rt_array_last",
                    _ => "rt_array_pop",
                };
                let needs_int_unbox = matches!(
                    element_ty,
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
                let needs_float_unbox = matches!(element_ty, TypeId::F32 | TypeId::F64);
                if needs_int_unbox || needs_float_unbox {
                    return self.with_func(|func, current_block| {
                        let raw_result = func.new_vreg();
                        let unboxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(raw_result),
                            target: crate::mir::effects::CallTarget::from_name(rt_name),
                            args: vec![receiver_reg],
                        });
                        if needs_int_unbox {
                            block.instructions.push(MirInst::UnboxInt {
                                dest: unboxed,
                                value: raw_result,
                            });
                        } else {
                            block.instructions.push(MirInst::UnboxFloat {
                                dest: unboxed,
                                value: raw_result,
                            });
                        }
                        unboxed
                    });
                }
            }
        }

        let is_array_append_method = method == "push" || method == "append";

        if is_array_append_method
            && args.len() == 1
            && self
                .type_registry
                .and_then(|tr| tr.get(receiver.ty))
                .is_some_and(|ty| matches!(ty, crate::hir::HirType::Array { element, .. } if *element == TypeId::U8))
        {
            // The push helper returns bool (success), NOT the array. The value of
            // the `arr.push(x)` expression must be the (in-place mutated) array
            // itself, so `arr = arr.push(x)` keeps a valid array pointer instead
            // of overwriting it with `true` (raw 1 == heap-tagged null).
            return self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: crate::mir::effects::CallTarget::from_name("rt_typed_bytes_u8_push"),
                    args: vec![receiver_reg, arg_regs[0]],
                });
                receiver_reg
            });
        }
        if is_array_append_method
            && args.len() == 1
            && args[0].ty == TypeId::U32
            && self
                .type_registry
                .and_then(|tr| tr.get(receiver.ty))
                .is_some_and(|ty| matches!(ty, crate::hir::HirType::Array { element, .. } if *element == TypeId::U32))
        {
            // Push returns bool — yield the array as the expression value (see above).
            return self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: crate::mir::effects::CallTarget::from_name("rt_typed_words_u32_push"),
                    args: vec![receiver_reg, arg_regs[0]],
                });
                receiver_reg
            });
        }
        if is_array_append_method
            && args.len() == 1
            && args[0].ty == TypeId::U64
            && self
                .type_registry
                .and_then(|tr| tr.get(receiver.ty))
                .is_some_and(|ty| matches!(ty, crate::hir::HirType::Array { element, .. } if *element == TypeId::U64))
        {
            // Push returns bool — yield the array as the expression value (see above).
            return self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: crate::mir::effects::CallTarget::from_name("rt_typed_words_u64_push"),
                    args: vec![receiver_reg, arg_regs[0]],
                });
                receiver_reg
            });
        }

        // Box integer arguments for array .push() — matches IndexGet unbox at line 1236.
        // Without this, wrap_value (no-op) passes raw integers to rt_array_push,
        // but IndexGet + MIR UnboxInt expects tagged (val << 3) values.
        if is_array_append_method && !args.is_empty() {
            let push_arg_ty = args[0].ty;
            let receiver_element_is_function =
                self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(|ty| {
                    if let crate::hir::HirType::Array { element, .. } = ty {
                        self.type_registry
                            .and_then(|tr| tr.get(*element))
                            .is_some_and(|element_ty| matches!(element_ty, crate::hir::HirType::Function { .. }))
                    } else {
                        false
                    }
                });
            let needs_push_boxing = matches!(
                push_arg_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
                    | TypeId::BOOL
            ) && !receiver_element_is_function;
            // F32/F64 push args must go through BoxFloat (lossless rt_value_float
            // heap box), NOT raw: an untagged double's low mantissa bits read as a
            // runtime tag, so IndexGet's decode zeroed 3 mantissa bits —
            // `p.push(0.1); p[0] == 0.1` was false on the JIT path. Same fix the
            // array-literal lowering already has (lowering_expr_collection.rs).
            // See doc/08_tracking/bug/seed_f64_array_element_precision_mask_2026-07-19.md.
            let needs_push_float_boxing = matches!(push_arg_ty, TypeId::F32 | TypeId::F64)
                && !receiver_element_is_function;
            if needs_push_boxing || needs_push_float_boxing {
                let raw_arg = arg_regs[0];
                let use_float = needs_push_float_boxing;
                let boxed_arg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    if use_float {
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: raw_arg,
                        });
                    } else {
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: raw_arg,
                        });
                    }
                    boxed
                })?;
                arg_regs[0] = boxed_arg;
            }
        }

        // Box the `[T].index_of(v)` needle for the SAME reason `push` boxes its
        // argument just above: array elements are stored TAG-BOXED (see the
        // array-literal lowering's BoxInt/BoxFloat), and `rt_array_index_of`
        // compares them with `rt_value_eq`. A raw native int needle can never
        // equal a tagged element, so every `[i64].index_of(n)` returned -1 even
        // when the element was present at index 0 — while `[text].index_of(s)`
        // happened to work, because a string argument is already a tagged heap
        // pointer and needs no boxing. Gated on an array receiver so
        // `text.index_of(sub)` (which routes to rt_string_find) is untouched.
        if method == "index_of" && args.len() == 1 && self.receiver_is_array(receiver, receiver_local_ty) {
            let needle_ty = args[0].ty;
            let needs_needle_int_boxing = matches!(
                needle_ty,
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
            // Floats go through BoxFloat for the same lossless-tagging reason as
            // the push path (an untagged double's low mantissa bits read as a
            // runtime tag).
            let needs_needle_float_boxing = matches!(needle_ty, TypeId::F32 | TypeId::F64);
            if needs_needle_int_boxing || needs_needle_float_boxing {
                let raw_arg = arg_regs[0];
                let use_float = needs_needle_float_boxing;
                let boxed_arg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    if use_float {
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: raw_arg,
                        });
                    } else {
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: raw_arg,
                        });
                    }
                    boxed
                })?;
                arg_regs[0] = boxed_arg;
            }
        }

        if is_array_append_method && args.len() == 1 && self.receiver_is_array(receiver, receiver_local_ty) {
            // rt_array_push returns bool (success), NOT the array. The value of
            // the `arr.push(x)` expression must be the (in-place mutated) array
            // itself, so `arr = arr.push(x)` keeps a valid array pointer instead
            // of overwriting it with `true` (raw 1 == heap-tagged null pointer).
            // That exact overwrite corrupted ExprKind.Call payloads built by
            // `args = args.push(CallArg(...))` in flat_ast_bridge_part1 and
            // crashed the stage4 binary in flat_ast_to_module (2026-06-10).
            return self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: crate::mir::effects::CallTarget::from_name("rt_array_push"),
                    args: vec![receiver_reg, arg_regs[0]],
                });
                receiver_reg
            });
        }

        // Array merge/concat/extend: in-place append the other array's elements
        // (mirrors codegen's `("Array","merge")` arm — rt_array_len + extend).
        // Without this the call falls through to a static `Array.merge` symbol
        // call → rt_function_not_found at runtime. Latent in the compiled path;
        // exposed when adaa700d4e5 routed `run` through JIT/compiled by default.
        // Gated on receiver_is_array so String.concat is unaffected.
        if matches!(method, "merge" | "concat" | "extend")
            && args.len() == 1
            && self.receiver_is_array(receiver, receiver_local_ty)
        {
            return self.with_func(|func, current_block| {
                let count = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(count),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_len"),
                    args: vec![arg_regs[0]],
                });
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: crate::mir::effects::CallTarget::from_name("rt_array_extend_i64"),
                    args: vec![receiver_reg, arg_regs[0], count],
                });
                receiver_reg
            });
        }

        // Builtin primitive .to_string()/.to_text()/.str() routes to
        // rt_to_string, which expects a tagged RuntimeValue receiver rather than
        // a raw native scalar.
        //
        // Native `u64` values above the 61-bit tagged-int limit cannot be boxed
        // losslessly, so route them through an unsigned-specific bridge instead.
        if method == "to_string" || method == "to_text" || method == "str" {
            if receiver.ty == TypeId::U64 {
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::effects::CallTarget::from_name("rt_raw_u64_to_string"),
                        args: vec![receiver_reg],
                    });
                    dest
                });
            }
            let needs_int_boxing = matches!(
                receiver.ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            );
            let needs_float_boxing = matches!(receiver.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = receiver.ty == TypeId::BOOL;
            if needs_bool_boxing {
                receiver_reg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(boxed),
                        target: crate::mir::effects::CallTarget::from_name("rt_value_bool"),
                        args: vec![receiver_reg],
                    });
                    boxed
                })?;
            } else if needs_float_boxing {
                receiver_reg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxFloat {
                        dest: boxed,
                        value: receiver_reg,
                    });
                    boxed
                })?;
            } else if needs_int_boxing {
                receiver_reg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: receiver_reg,
                    });
                    boxed
                })?;
            }
        }

        // Try to qualify method name with receiver type (e.g., "TreeSitter.expect")
        // When `receiver.ty` is `Any` (which happens for cross-module
        // `var x = Imported.new()` where type inference cannot reach
        // into the imported constructor), `get_type_name` returns
        // None and the func_name falls through to the bare method
        // name. The native-build codegen then picks the shortest
        // `.<method>` symbol in the whole module — a silent miscall
        // that caused `shell.init()` to dispatch to `Ps2Keyboard.init`
        // on the x86_64 baremetal desktop lane (see Agent V's
        // 2026-04-13 workaround). Set SIMPLE_DEBUG_METHOD_DISPATCH=1
        // to dump these bare-name dispatches at compile time.
        //
        // Round-16 fix (sys-gui-006 Blocker 2): when the expression's
        // own `receiver.ty` cannot be named, fall back to the type
        // recorded on the corresponding `MirFunction.locals[idx]`
        // when the receiver is `HirExprKind::Local(idx)`. This is
        // exactly the user-supplied `var shell: DesktopShell = ...`
        // annotation — copied into the MIR local table by the
        // statement lowerer — and survives even when constructor
        // return-type inference falls through to `Any`. Without
        // this fallback the typed-receiver workaround at
        // `desktop_e2e_entry.spl:97` was being silently undone for
        // the very call site (`shell.init()`) it was meant to fix.
        //
        // Round-17 widening (T58 follow-up): non-Local receivers —
        // `self.widget.init()`, `container.pair.0.init()`,
        // `arr[i].init()` — would still mis-dispatch because their
        // `receiver.ty` is likewise Unknown/Any in the same
        // cross-module constructor scenarios. Recover the type by
        // walking one structural hop into the sub-expression: look
        // up the field's type on the struct type of the base, the
        // tuple element type at the given index, or the array/vec
        // element type. Each hop uses only registered type info
        // from `TypeRegistry` — no synthesis — and the recursion
        // terminates at a Local (or an expression whose own `ty`
        // is already named).
        //
        // DEFENSE-IN-DEPTH (bug simpleos_native_build_bare_len_dynamic_dispatch_symbol_collision,
        // 2026-07-16): `Result`/`Option` are builtin wrapper enums with no
        // real methods of their own. If a `?`-unwrap (or any other upstream
        // bug) ever leaves a receiver still typed as the wrapper instead of
        // its unwrapped payload, qualifying a builtin-collision method
        // (`len`/`is_empty`/`contains`/...) as "Result.<method>" would still
        // not exist as a real symbol: `get_type_name` succeeds (the type
        // genuinely IS named "Result"), so none of the erased-receiver
        // fallbacks below ever fire, and codegen's suffix-based resolution
        // binds the qualified-but-nonexistent name to an unrelated
        // same-named method elsewhere in the link (e.g. `BinaryWriter.len`,
        // observed crashing on a tagged text value). Treat a Result/Option
        // receiver as erased for exactly these collision-prone names so it
        // is forced through the safe runtime tag-dispatching path instead
        // (mirrors the existing `receiver_is_array` -> `rt_array_len`
        // special case, generalized via `is_bare_builtin_collection_method`
        // + `try_compile_builtin_method_call` / `rt_len` in codegen).
        let wrapper_enum_builtin_collision = [Some(receiver.ty), receiver_local_ty]
            .into_iter()
            .flatten()
            .find_map(|ty| self.type_registry.and_then(|r| r.get_type_name(ty)))
            .is_some_and(|name| name == "Result" || name == "Option")
            && crate::codegen::instr::closures_structs::is_bare_builtin_collection_method(method, args.len());

        let func_name = if wrapper_enum_builtin_collision {
            if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                eprintln!(
                    "[MIR-METHOD-DISPATCH] '{}' receiver resolved to Result/Option wrapper; routing as erased builtin instead of a nonexistent qualified method",
                    method
                );
            }
            method.to_string()
        } else if let Some(registry) = self.type_registry {
            if let Some(type_name) = registry.get_type_name(receiver.ty) {
                format!("{}.{}", type_name, method)
            } else if let Some(type_name) = self.builtin_method_receiver_name(receiver.ty) {
                format!("{}.{}", type_name, method)
            } else if let Some(local_ty) = receiver_local_ty {
                if let Some(type_name) = registry.get_type_name(local_ty) {
                    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                        eprintln!(
                            "[MIR-METHOD-DISPATCH] '{}' qualified via local-table type '{}' (receiver.ty was unnamed)",
                            method, type_name
                        );
                    }
                    format!("{}.{}", type_name, method)
                } else if let Some(type_name) = self.builtin_method_receiver_name(local_ty) {
                    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                        eprintln!(
                            "[MIR-METHOD-DISPATCH] '{}' qualified via builtin type '{}' (receiver.ty was unnamed)",
                            method, type_name
                        );
                    }
                    format!("{}.{}", type_name, method)
                } else {
                    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                        let ty_desc = registry
                            .get(receiver.ty)
                            .map(|t| format!("{:?}", t))
                            .unwrap_or_else(|| format!("<missing tid={:?}>", receiver.ty));
                        eprintln!(
                            "[MIR-METHOD-DISPATCH] bare '{}' call: receiver ty = {} (local-table fallback also unnamed)",
                            method, ty_desc
                        );
                    }
                    method.to_string()
                }
            } else {
                if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                    let ty_desc = registry
                        .get(receiver.ty)
                        .map(|t| format!("{:?}", t))
                        .unwrap_or_else(|| format!("<missing tid={:?}>", receiver.ty));
                    eprintln!(
                        "[MIR-METHOD-DISPATCH] bare '{}' call: receiver ty = {}",
                        method, ty_desc
                    );
                }
                method.to_string()
            }
        } else {
            method.to_string()
        };

        let dispatch_receiver_ty = receiver_local_ty.unwrap_or(receiver.ty);
        match dispatch {
            DispatchMode::Dynamic => {
                // Try to find the method in a registered trait (vtable dispatch).
                // Receiver-aware: `func_name` was qualified as "Type.method" above
                // whenever the receiver's static type is known — pass that type so
                // concrete classes that merely share a method name with a trait
                // get static dispatch instead of a bogus vtable load.
                let recv_type_name: Option<&str> = func_name.rsplit_once('.').map(|(ty, _)| ty);
                if let Some((vtable_slot, param_types, return_type)) =
                    self.find_trait_for_method_on_receiver(method, recv_type_name)
                {
                    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                        eprintln!(
                            "[MIR-METHOD-DISPATCH] '{}' lowered as virtual trait call at slot {}",
                            method, vtable_slot
                        );
                    }
                    let dest = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::MethodCallVirtual {
                            dest: Some(dest),
                            receiver: receiver_reg,
                            vtable_slot,
                            param_types,
                            return_type,
                            args: arg_regs,
                        });
                        dest
                    })?;
                    Ok(dest)
                } else {
                    self.box_method_args_for_any_params(&func_name, args, &mut arg_regs)?;
                    // Fallback: not a registered trait method — use static dispatch
                    let dest = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::MethodCallStatic {
                            dest: Some(dest),
                            receiver: receiver_reg,
                            func_name,
                            args: arg_regs,
                        });
                        dest
                    })?;

                    // NOTE: Do NOT store the push result back to the receiver
                    // variable. rt_array_push returns bool (success/failure),
                    // NOT a new array pointer. Storing the bool back would
                    // overwrite the array pointer with 1 (true), causing
                    // crashes on subsequent array access.
                    // The array is mutated in-place; the pointer stays valid.

                    Ok(dest)
                }
            }
            DispatchMode::Static => {
                self.box_method_args_for_any_params(&func_name, args, &mut arg_regs)?;
                let dest = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::MethodCallStatic {
                        dest: Some(dest),
                        receiver: receiver_reg,
                        func_name,
                        args: arg_regs,
                    });
                    dest
                })?;

                // NOTE: Do NOT store the push result back to the receiver
                // variable. rt_array_push returns bool (success/failure),
                // NOT a new array pointer. Storing the bool back would
                // overwrite the array pointer with 1 (true), causing
                // crashes on subsequent array access.
                // The array is mutated in-place; the pointer stays valid.

                Ok(dest)
            }
        }
    }
}

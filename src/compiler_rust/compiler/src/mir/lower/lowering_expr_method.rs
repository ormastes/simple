//! Method call expression lowering (static and dynamic dispatch).

use super::lowering_core::{MirLowerResult, MirLowerer};
use super::lowering_di::builtin_type_name;
use crate::hir::{BinOp, DispatchMode, HirExpr, HirType, TypeId};
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
        // Step (d), 2026-08-02: delegate to the SINGLE authoritative definition
        // in the runtime crate. This value is a RUNTIME ABI, not a
        // compiler-internal convention: `rt_option_some`/`rt_option_none`
        // (runtime/src/value/objects.rs) build Option values with it, the
        // bytecode compiler emits it into the instruction stream, and the
        // interpreter SFFI reads it back. A second copy here that drifted by
        // one character would desynchronize compiled code from the runtime
        // silently. See
        // doc/08_tracking/bug/enum_bare_name_collision_registry_2026-08-01.md.
        simple_runtime::value::hash_variant_discriminant(variant_name) as i64
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
                "bytes" if effective_ty == TypeId::STRING => {
                    // The receiver type is authoritative.  Leaving this as a
                    // name-dispatched method lets a same-leaf user method
                    // (for example `PointerSize.bytes`) capture the call when
                    // the module-wide import map is built.
                    return self.lower_builtin_call_expr(
                        "rt_string_bytes",
                        std::slice::from_ref(receiver),
                        TypeId::ANY,
                    );
                }
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

        // `d.insert(k, v)` / `d.set(k, v)` on a Dict<K, V> are routed by
        // codegen (codegen/instr/closures_structs.rs `"set" | "insert"`,
        // codegen/llvm/functions.rs `("Dict"|"dict", "set") | (.., "insert")`)
        // onto the SAME `rt_dict_set` runtime symbol the dict LITERAL uses.
        // `rt_dict_set(dict, key, value)` requires TAGGED RuntimeValues for
        // both key and value (see lowering_expr_collection.rs
        // `lower_dict_expr`'s comment) — but the generic dotted-name
        // method-call path below lowers `args` RAW with no boxing, and the
        // codegen routing just forwards those two vregs verbatim as
        // `key_val`/`val_val`. Text keys/values are unaffected (strings are
        // already heap RuntimeValue pointers), which is why
        // `{"a":1}.insert("b",2)` looked correct — but an int KEY stored raw
        // hashes into a different bucket than the boxed key every read path
        // uses, so `{1:10}.insert(2,20)` then `d[2]` silently returned the
        // nil sentinel (3) instead of 20. Emit our own boxed `rt_dict_set`
        // call here, bypassing the generic path entirely, mirroring exactly
        // how `d[k] = v` index-assignment boxes key and value
        // (lowering_stmt.rs `HirExprKind::Index` write arm): box int keys
        // unconditionally, box int values UNLESS the dict's value type is a
        // heap type (struct/enum/etc — boxing a heap pointer would corrupt
        // its tag, task #117).
        // See task: dict_insert_integer_key_boxing.
        if (method == "set" || method == "insert")
            && args.len() == 2
            && self.receiver_is_dict(receiver, receiver_local_ty)
        {
            fn needs_int_boxing(t: TypeId) -> bool {
                matches!(
                    t,
                    TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                )
            }
            let value_is_heap = self
                .type_registry
                .and_then(|tr| {
                    tr.get(receiver.ty)
                        .or_else(|| receiver_local_ty.and_then(|ty| tr.get(ty)))
                })
                .and_then(|ty| match ty {
                    HirType::Dict { value, .. } => Some(*value),
                    _ => None,
                })
                .is_some_and(|t| {
                    t != TypeId::ANY
                        && !matches!(
                            t,
                            TypeId::I8
                                | TypeId::I16
                                | TypeId::I32
                                | TypeId::I64
                                | TypeId::U8
                                | TypeId::U16
                                | TypeId::U32
                                | TypeId::U64
                                | TypeId::F32
                                | TypeId::F64
                                | TypeId::BOOL
                        )
                });

            let receiver_reg = self.lower_expr(receiver)?;

            let raw_key_reg = self.lower_expr(&args[0])?;
            let key_reg = if args[0].ty == TypeId::U64 {
                self.box_u64_runtime_value(raw_key_reg)?
            } else if needs_int_boxing(args[0].ty) {
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: raw_key_reg,
                    });
                    boxed
                })?
            } else {
                raw_key_reg
            };

            let raw_value_reg = self.lower_expr(&args[1])?;
            let value_reg = if !value_is_heap && args[1].ty == TypeId::U64 {
                self.box_u64_runtime_value(raw_value_reg)?
            } else if !value_is_heap && needs_int_boxing(args[1].ty) {
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: raw_value_reg,
                    });
                    boxed
                })?
            } else {
                raw_value_reg
            };

            let target = crate::mir::effects::CallTarget::from_name("rt_dict_set");
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target,
                    args: vec![receiver_reg, key_reg, value_reg],
                });
                dest
            });
        }

        // `d.get_or(k, default)` on a Dict<K, V>: return the value if `k` is
        // present, else `default` — mirroring the interpreter's
        // `interpreter_method/collections.rs` "get_or" arm EXACTLY: presence
        // is decided by `map.get(&key)` (a contains-key test), NOT by
        // comparing the stored value against a nil sentinel. A present entry
        // whose value happens to equal the nil-sentinel encoding (3, per the
        // `char_code_at`/`index_of` tag-collision bug class) must still win
        // over `default` — so this lowers to a REAL branch on
        // `rt_dict_contains`, not a "is result == sentinel" check.
        //
        // There is NO `rt_dict_get_or` runtime symbol (verified: absent from
        // both `codegen/runtime_sffi.rs` and `common/src/runtime_symbols.rs`,
        // and the JIT's import-resolution guard in `codegen/jit.rs` demotes
        // the WHOLE module to the interpreter — silently — if any declared
        // import is unresolved). So this expands to two calls that DO already
        // have real runtime symbols: `rt_contains` (same symbol `.has()` /
        // `.contains_key()` already route to, see
        // `codegen/instr/closures_structs.rs` `"contains_key" | "has_key" |
        // "has" => "rt_contains"`) for the presence test, and `rt_index_get`
        // (same symbol `d[k]`/`d.get(k)` use, see `lower_index_expr` above)
        // for the value read — followed by the SAME UnboxInt/UnboxFloat/Cast
        // tail as `d[k]`/`d.get(k)` via `unbox_dict_read_result`, so int/float
        // values are correctly unboxed and heap values pass through verbatim.
        // Both `rt_contains` and `rt_index_get` hash-lookup by the SAME
        // tagged key (`codegen/instr/closures_structs.rs`
        // `box_dict_key = matches!(runtime_func, "rt_index_get" |
        // "rt_dict_remove" | "rt_contains")`), so the int key is boxed ONCE
        // here and the identical boxed vreg is reused for both calls —
        // matching `d[k]`/`.get(k)`'s boxing and avoiding a mismatched-hash
        // miss (task: dict_insert_integer_key_boxing).
        //
        // Receiver and key are each evaluated exactly ONCE (into `receiver_reg`
        // / `key_reg`) and reused across both runtime calls, so a
        // side-effecting receiver/key expression is not evaluated twice.
        if method == "get_or" && args.len() == 2 && self.receiver_is_dict(receiver, receiver_local_ty) {
            use crate::mir::effects::LocalKind;
            use crate::mir::function::MirLocal;

            fn needs_int_boxing(t: TypeId) -> bool {
                matches!(
                    t,
                    TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                )
            }

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

            let receiver_reg = self.lower_expr(receiver)?;

            let raw_key_reg = self.lower_expr(&args[0])?;
            let key_reg = if args[0].ty == TypeId::U64 {
                self.box_u64_runtime_value(raw_key_reg)?
            } else if needs_int_boxing(args[0].ty) {
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: raw_key_reg,
                    });
                    boxed
                })?
            } else {
                raw_key_reg
            };

            // The interpreter (`interpreter_method/collections.rs` "get_or")
            // evaluates `default` EAGERLY, unconditionally, before checking
            // presence — `eval_arg(args, 1, ...)` runs regardless of hit or
            // miss. Match that exactly: lower `default` here, before the
            // branch, not lazily inside the else-arm (a lazy default would
            // skip a side-effecting default expression on a hit, diverging
            // from the interpreter).
            let default_reg = self.lower_expr(&args[1])?;

            // cond = rt_contains(dict, key) — u8 0/1, coerced by the Branch
            // terminator codegen (codegen/instr/body.rs: brif expects i8).
            let cond_reg = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_contains"),
                    args: vec![receiver_reg, key_reg],
                });
                dest
            })?;

            // Merge-value temp local, same pattern as `lower_if_expr`.
            let temp_local_index = self.with_func(|func, _| {
                let index = func.params.len() + func.locals.len();
                func.locals.push(MirLocal {
                    name: format!("$get_or_merge_{}", index),
                    ty: value_ty,
                    kind: LocalKind::Local,
                    is_ghost: false,
                });
                index
            })?;
            let temp_addr = self.with_func(|func, current_block| {
                let addr = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::LocalAddr {
                    dest: addr,
                    local_index: temp_local_index,
                });
                addr
            })?;

            let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                let then_id = func.new_block();
                let else_id = func.new_block();
                let merge_id = func.new_block();
                let block = func.block_mut(current_block).unwrap();
                block.terminator = crate::mir::Terminator::Branch {
                    cond: cond_reg,
                    then_block: then_id,
                    else_block: else_id,
                };
                (then_id, else_id, merge_id)
            })?;

            // then: present — read + unbox exactly like `d[k]` / `d.get(k)`.
            self.set_current_block(then_id)?;
            let raw_result = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_index_get"),
                    args: vec![receiver_reg, key_reg],
                });
                dest
            })?;
            let then_value = self.unbox_dict_read_result(raw_result, value_ty)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: temp_addr,
                    value: then_value,
                    ty: value_ty,
                });
            })?;
            self.finalize_block_jump(merge_id)?;

            // else: absent — store the already-evaluated `default_reg`
            // (computed eagerly above, matching the interpreter).
            self.set_current_block(else_id)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: temp_addr,
                    value: default_reg,
                    ty: value_ty,
                });
            })?;
            self.finalize_block_jump(merge_id)?;

            // merge: load the result.
            self.set_current_block(merge_id)?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Load {
                    dest,
                    addr: temp_addr,
                    ty: value_ty,
                });
                dest
            });
        }

        // === JIT method-dispatch audit batch (jit_method_dispatch_audit_2026-07-29) ===
        // `arr.sum()` on an Array<T>: the interpreter
        // (interpreter_method/collections.rs "sum") only accumulates Int
        // elements (ignoring anything that isn't `Value::Int`) and always
        // returns an Int — never a Float, even when the array holds floats.
        // `rt_array_sum` (runtime/src/value/collections.rs) mixes floats in
        // and can return a Float when the array holds any float element — a
        // known, documented divergence from the interpreter for MIXED
        // int/float arrays only; for a pure-Int array (the overwhelmingly
        // common case) both agree exactly. `rt_array_sum` already returns a
        // TAG-BOXED int (`RuntimeValue::from_int`), matching what `d[k]`/
        // `.get(k)` return for an Int value, so reuse the same tag-boxing-
        // safe unbox helper `unbox_dict_read_result` (lowering_expr_struct.rs)
        // `get_or` introduced.
        if method == "sum" && args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            let raw_result = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_sum"),
                    args: vec![receiver_reg],
                });
                dest
            })?;
            return self.unbox_dict_read_result(raw_result, TypeId::I64);
        }

        // `arr.max()` / `arr.min()` on an Array<T>: mirrors the interpreter's
        // "max"/"min" (interpreter_method/collections.rs) exactly —
        // element-wise compare (Int/Float/Str), Nil for an empty array.
        // `rt_array_max`/`rt_array_min` already return the TAG-BOXED stored
        // element (or NIL), same shape as `rt_array_first`/`rt_array_last`/
        // `d[k]` — reuse the same unbox helper, typed by the array's element
        // type (ANY when unknown), matching the `"first" | "last" | "get" |
        // "max" | "min"` table entry in hir/lower/expr/mod.rs.
        if (method == "max" || method == "min")
            && args.is_empty()
            && self.receiver_is_array(receiver, receiver_local_ty)
        {
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
            let receiver_reg = self.lower_expr(receiver)?;
            let runtime_fn = if method == "max" {
                "rt_array_max"
            } else {
                "rt_array_min"
            };
            let raw_result = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name(runtime_fn),
                    args: vec![receiver_reg],
                });
                dest
            })?;
            return self.unbox_dict_read_result(raw_result, element_ty);
        }

        // `arr.take(n)` / `arr.skip(n)` / `arr.drop(n)` on an Array<T>:
        // mirrors the interpreter's "take" / "skip"|"drop"
        // (interpreter_method/collections.rs) — both clamp to [0, len] and
        // return a NEW array, never mutate the receiver. `rt_array_take`/
        // `rt_array_drop` take a RAW (non-tag-boxed) i64 count — same
        // convention as `rt_array_extend_i64`'s count argument just below —
        // and return a fresh array pointer, which needs no unboxing (arrays
        // are already valid RuntimeValue pointers, matching `"slice" |
        // "filter" | "map"` in hir/lower/expr/mod.rs). Known divergence,
        // documented not fixed: for a NEGATIVE `n`, the interpreter's
        // `eval_arg_usize` casts `i64 as usize`, wrapping to a huge value (so
        // `take(-1)` behaves like "take all" and `skip(-1)` like "skip
        // nothing"), while `rt_array_take`/`rt_array_drop` clamp negative `n`
        // to 0 (so `take(-1)` returns empty and `skip(-1)` returns
        // everything) — the exact opposite. Non-negative `n` (the
        // overwhelmingly common case) matches exactly.
        if matches!(method, "take" | "skip" | "drop")
            && args.len() == 1
            && self.receiver_is_array(receiver, receiver_local_ty)
        {
            let receiver_reg = self.lower_expr(receiver)?;
            let n_reg = self.lower_expr(&args[0])?;
            let runtime_fn = if method == "take" {
                "rt_array_take"
            } else {
                "rt_array_drop"
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name(runtime_fn),
                    args: vec![receiver_reg, n_reg],
                });
                dest
            });
        }

        // `d.entries()` on a Dict<K, V>: mirrors the interpreter's
        // "entries"|"items" (interpreter_method/collections.rs) — an array
        // of (key, value) tuples. `rt_dict_entries` (runtime/src/value/
        // dict.rs) already exists and already had a linker manifest entry
        // (common/src/runtime_symbols.rs, "for-in iteration over
        // dicts/arrays") but was never declared in the codegen SFFI table
        // (codegen/runtime_sffi.rs) or wired to a dispatch arm, so it fell
        // through to `rt_method_not_found`. Returns a fresh array pointer —
        // no unboxing needed, matching the existing `"items" | "entries" =>
        // Some(TypeId::ANY)` table entry in hir/lower/expr/mod.rs. Known
        // divergence, documented not fixed: the interpreter's `entries`
        // iterates in canonical sorted-by-key order
        // (`dict_entries_sorted`); `rt_dict_entries` returns raw hashmap
        // order (the SAME already-known `dict.keys()`/`dict.values()`
        // ordering gap the audit doc calls out separately) — the result SET
        // matches, the SEQUENCE does not.
        if method == "entries" && args.is_empty() && self.receiver_is_dict(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_dict_entries"),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `s.count(needle)` on a String: the interpreter
        // (interpreter_method/string.rs "count") is
        // `s.matches(&needle).count()` — the count of NON-OVERLAPPING
        // occurrences of `needle` in `s`. There is no `rt_string_count`
        // runtime symbol (confirmed absent from runtime/src/value/
        // collections.rs and codegen/runtime_sffi.rs) and the task brief for
        // this batch forbids adding new runtime Rust, so this expands over
        // TWO existing runtime calls: `rt_string_split` (whose byte-split
        // kernel, runtime/src/value/byte_kernels.rs
        // `scalar_byte_split_ranges`, performs the SAME non-overlapping
        // left-to-right scan Rust's `str::matches` does) and `rt_array_len`.
        // `split(s, needle).len() - 1` equals the non-overlapping match
        // count for any NON-EMPTY needle. Known divergence, documented not
        // fixed: for an EMPTY needle (`s.count("")`), the interpreter's
        // `matches("").count()` is `len+1` (chars + 1 boundary matches) but
        // `scalar_byte_split_ranges` for an empty delimiter yields one range
        // per char boundary INCLUDING the trailing one (`len+1` ranges), so
        // this expansion computes `len+1 - 1 = len` — off by one from the
        // interpreter for the empty-needle case only. Non-empty-needle
        // callers (the overwhelmingly common case and the one this fix
        // targets) match exactly.
        if method == "count" && args.len() == 1 && receiver_local_ty.unwrap_or(receiver.ty) == TypeId::STRING {
            let receiver_reg = self.lower_expr(receiver)?;
            let needle_reg = self.lower_expr(&args[0])?;
            return self.with_func(|func, current_block| {
                let parts = func.new_vreg();
                let len_raw = func.new_vreg();
                let one = func.new_vreg();
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(parts),
                    target: crate::mir::effects::CallTarget::from_name("rt_string_split"),
                    args: vec![receiver_reg, needle_reg],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(len_raw),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_len"),
                    args: vec![parts],
                });
                block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
                block.instructions.push(MirInst::BinOp {
                    dest,
                    op: BinOp::Sub,
                    left: len_raw,
                    right: one,
                });
                dest
            });
        }

        // `s.appended(x)` / `s.prepended(x)` on a String: the interpreter
        // (interpreter_method/string.rs "appended"/"prepended") is exactly
        // `concat(s, x)` / `concat(x, s)` — `rt_string_concat` (runtime/
        // src/value/collections.rs) already exists and already backs the
        // `"concat"` method (see codegen/instr/methods.rs), so this is just a
        // second dispatch-arm name over the same existing call with the
        // operand order swapped for `prepended`. Confirmed live before this
        // fix: JIT `[jit-addr]` + `Function 'str.appended'/'str.prepended'
        // not found`; interpreter `"abc".appended("d")` == `"abcd"`,
        // `"abc".prepended("z")` == `"zabc"`. Result is a fresh string
        // pointer — no unboxing needed (strings are already valid
        // RuntimeValue pointers, same as arrays).
        if matches!(method, "appended" | "prepended")
            && args.len() == 1
            && receiver_local_ty.unwrap_or(receiver.ty) == TypeId::STRING
        {
            let receiver_reg = self.lower_expr(receiver)?;
            let arg_reg = self.lower_expr(&args[0])?;
            let (left, right) = if method == "appended" {
                (receiver_reg, arg_reg)
            } else {
                (arg_reg, receiver_reg)
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_string_concat"),
                    args: vec![left, right],
                });
                dest
            });
        }

        // `arr.insert(idx, item)` on an Array<T>: the interpreter
        // (interpreter_method/collections.rs "insert") — `idx <= len` ->
        // insert `item` at `idx` (idx == len means append); `idx > len` ->
        // return an UNCHANGED COPY of the receiver (no error, no
        // truncation). Always returns a brand-new array (never mutates the
        // receiver) — same non-mutating shape as `concat`/`merge` just
        // below. There is no `rt_array_insert` runtime symbol (confirmed
        // absent from runtime/src/value/collections.rs and
        // codegen/runtime_sffi.rs — the entry in method_registry/builtins.rs
        // is aspirational metadata only, not wired to codegen) and the task
        // brief forbids adding new runtime Rust for this lane, so this
        // expands over EXISTING runtime calls: `rt_slice` (splits the
        // receiver into its `0..idx` and `idx..len` halves), `rt_array_new`
        // + `rt_array_push` (wraps the inserted item as a 1-element array so
        // it can be spliced back in), and `rt_array_concat` (recombines the
        // three pieces). Follows the SAME then/else-branch/merge-block shape
        // `Dict.get_or` uses above (task: dict_get_or_jit_not_found) for the
        // `idx <= len` test.
        if method == "insert" && args.len() == 2 && self.receiver_is_array(receiver, receiver_local_ty) {
            use crate::mir::effects::LocalKind;
            use crate::mir::function::MirLocal;

            let receiver_reg = self.lower_expr(receiver)?;
            let idx_reg = self.lower_expr(&args[0])?;
            let item_reg_raw = self.lower_expr(&args[1])?;

            // Box the inserted item exactly like `.push()` does — array
            // elements are stored TAG-BOXED, and `rt_array_push` (used to
            // build the 1-element splice array below) stores by that
            // convention.
            let item_ty = args[1].ty;
            let needs_item_int_boxing = matches!(
                item_ty,
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
            let needs_item_float_boxing = matches!(item_ty, TypeId::F32 | TypeId::F64);
            let item_reg = if item_ty == TypeId::U64 {
                self.box_u64_runtime_value(item_reg_raw)?
            } else if needs_item_int_boxing || needs_item_float_boxing {
                let use_float = needs_item_float_boxing;
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    if use_float {
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: item_reg_raw,
                        });
                    } else {
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: item_reg_raw,
                        });
                    }
                    boxed
                })?
            } else {
                item_reg_raw
            };

            let len_reg = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_len"),
                    args: vec![receiver_reg],
                });
                dest
            })?;

            // cond = idx <= len (i8, Branch-ready — see codegen/instr/core.rs
            // `IntCC::SignedLessThanOrEqual` -> `icmp` returning i8).
            let cond_reg = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BinOp {
                    dest,
                    op: BinOp::LtEq,
                    left: idx_reg,
                    right: len_reg,
                });
                dest
            })?;

            // Merge-value temp local, same pattern as `Dict.get_or` above.
            let temp_local_index = self.with_func(|func, _| {
                let index = func.params.len() + func.locals.len();
                func.locals.push(MirLocal {
                    name: format!("$array_insert_merge_{}", index),
                    ty: receiver.ty,
                    kind: LocalKind::Local,
                    is_ghost: false,
                });
                index
            })?;
            let temp_addr = self.with_func(|func, current_block| {
                let addr = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::LocalAddr {
                    dest: addr,
                    local_index: temp_local_index,
                });
                addr
            })?;

            let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                let then_id = func.new_block();
                let else_id = func.new_block();
                let merge_id = func.new_block();
                let block = func.block_mut(current_block).unwrap();
                block.terminator = crate::mir::Terminator::Branch {
                    cond: cond_reg,
                    then_block: then_id,
                    else_block: else_id,
                };
                (then_id, else_id, merge_id)
            })?;

            // then: idx <= len — splice: slice(0,idx) ++ [item] ++ slice(idx,len).
            self.set_current_block(then_id)?;
            let inserted = self.with_func(|func, current_block| {
                let zero = func.new_vreg();
                let one = func.new_vreg();
                let left = func.new_vreg();
                let right = func.new_vreg();
                let item_arr = func.new_vreg();
                let pushed = func.new_vreg();
                let spliced = func.new_vreg();
                let result = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest: zero, value: 0 });
                block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
                block.instructions.push(MirInst::Call {
                    dest: Some(left),
                    target: crate::mir::effects::CallTarget::from_name("rt_slice"),
                    args: vec![receiver_reg, zero, idx_reg, one],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(right),
                    target: crate::mir::effects::CallTarget::from_name("rt_slice"),
                    args: vec![receiver_reg, idx_reg, len_reg, one],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(item_arr),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_new"),
                    args: vec![one],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(pushed),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_push"),
                    args: vec![item_arr, item_reg],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(spliced),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_concat"),
                    args: vec![left, item_arr],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(result),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_concat"),
                    args: vec![spliced, right],
                });
                let _ = pushed;
                result
            })?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: temp_addr,
                    value: inserted,
                    ty: receiver.ty,
                });
            })?;
            self.finalize_block_jump(merge_id)?;

            // else: idx > len — unchanged copy of the receiver.
            self.set_current_block(else_id)?;
            let copied = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_copy"),
                    args: vec![receiver_reg],
                });
                dest
            })?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: temp_addr,
                    value: copied,
                    ty: receiver.ty,
                });
            })?;
            self.finalize_block_jump(merge_id)?;

            // merge: load the result.
            self.set_current_block(merge_id)?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Load {
                    dest,
                    addr: temp_addr,
                    ty: receiver.ty,
                });
                dest
            });
        }

        // === JIT method-dispatch audit batch 2 (jit_method_dispatch_audit_2026-07-29,
        // lane DISPATCH2) === `arr.copy()` / `arr.clone()` on an Array<T>: the
        // interpreter (interpreter_method/collections.rs `"copy" | "clone"`)
        // returns a shallow copy — never mutates the receiver.
        // `rt_array_copy` (runtime/src/value/collections.rs) already exists
        // and already had a linker manifest entry but no dispatch arm here,
        // so it fell through to `rt_method_not_found`. Returns a fresh array
        // pointer of the SAME element type as the receiver — no unboxing
        // needed, matching the `"slice" | "filter" | "map" =>
        // Some(receiver.ty)` table entry in hir/lower/expr/mod.rs.
        if matches!(method, "copy" | "clone") && args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty)
        {
            let receiver_reg = self.lower_expr(receiver)?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_copy"),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `arr.unique()` / `arr.sorted()` / `arr.reversed()` on an Array<T>:
        // all three are the interpreter's non-mutating "return a NEW array"
        // siblings of `sort`/`reverse` (which already work OK per the audit —
        // those mutate in place). `rt_array_unique`/`rt_array_sorted`/
        // `rt_array_reversed` (runtime/src/value/collections.rs) already
        // exist, unused by any dispatch arm. Same shape as `arr.copy()` just
        // above — fresh array pointer, same element type, no unboxing.
        if matches!(method, "unique" | "sorted" | "reversed")
            && args.is_empty()
            && self.receiver_is_array(receiver, receiver_local_ty)
        {
            let receiver_reg = self.lower_expr(receiver)?;
            let runtime_fn = match method {
                "unique" => "rt_array_unique",
                "sorted" => "rt_array_sorted",
                _ => "rt_array_reversed",
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name(runtime_fn),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `arr.sort_desc()` on an Array<T>: the interpreter
        // (interpreter_method/collections.rs "sort_desc") builds a brand-new
        // `Vec` via `.to_vec()` then `sort_by` with reversed comparators —
        // same non-mutating "return a NEW array" shape as `unique`/`sorted`/
        // `reversed` just above, NOT the in-place mutation `array.fill` was
        // skipped for. `rt_array_sort_desc` (runtime/src/value/
        // collections.rs) is NOT 1:1 here: it sorts+reverses the receiver
        // ARRAY IN PLACE and returns a bool (mirrors `rt_array_reverse`'s
        // shape, not `rt_array_reversed`'s), which would silently mutate the
        // caller's array — the exact same mismatch class the guide's
        // `array.fill` skip note describes. Confirmed live: JIT
        // `[jit-addr]` + `Function 'Array.sort_desc' not found`; interpreter
        // on `[3,1,2].sort_desc()` returns a NEW `[3, 2, 1]` and leaves the
        // original binding usable. Fix: compose two EXISTING non-mutating
        // calls already used by the arm above — `rt_array_sorted` (ascending
        // copy) then `rt_array_reversed` (descending copy of that) — giving
        // the same descending-sorted NEW array with zero new runtime Rust.
        if method == "sort_desc" && args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            return self.with_func(|func, current_block| {
                let sorted = func.new_vreg();
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(sorted),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_sorted"),
                    args: vec![receiver_reg],
                });
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_reversed"),
                    args: vec![sorted],
                });
                dest
            });
        }

        // `arr.zip(other)` on an Array<T>: the interpreter
        // (interpreter_method/collections.rs "zip") pairs elements
        // pointwise into `(a, b)` tuples, truncated to the shorter array's
        // length. `rt_array_zip` (runtime/src/value/collections.rs) already
        // exists, takes both arrays directly and returns a fresh
        // array-of-tuples pointer — no unboxing needed, same shape as
        // `rt_array_copy`/`rt_array_flatten` above. Known open gap (NOT
        // fixed here, out of this lane's file-ownership scope): the
        // resulting tuples share the same JIT nested-tuple Display gap as
        // `array.enumerate` (jit_method_dispatch_audit_2026-07-29) — `len()`
        // and indexed element access are correct, only `print()`/
        // `to_string()` on an individual tuple element is affected.
        if method == "zip" && args.len() == 1 && self.receiver_is_array(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            let other_reg = self.lower_expr(&args[0])?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_zip"),
                    args: vec![receiver_reg, other_reg],
                });
                dest
            });
        }

        // `arr.flatten()` on an Array<Array<T>>: the interpreter's
        // (interpreter_method/collections.rs) one-level flatten.
        // `rt_array_flatten` already exists; result element type is not
        // statically resolvable from the outer array's declared type in
        // general (nested arrays are frequently ANY-typed), so this is typed
        // ANY in hir/lower/expr/mod.rs — matching the existing `"items" |
        // "entries" => Some(TypeId::ANY)` precedent for a dynamically-shaped
        // result.
        if method == "flatten" && args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_flatten"),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `arr.all_truthy()` / `arr.any_truthy()` on an Array<T>: the
        // interpreter (interpreter_method/collections.rs) checks truthiness
        // with no predicate lambda (the lambda-taking `all`/`any` are a
        // separate, out-of-scope DEMOTED class per the audit).
        // `rt_array_all_truthy`/`rt_array_any_truthy` already return a raw
        // (non-tag-boxed) `i64` 0/1 — same raw-representation contract as
        // `index_of`'s raw i64, which needs no manual boxing in this arm
        // because the HIR result type (`TypeId::BOOL` here, added to
        // hir/lower/expr/mod.rs) drives the generic downstream int/bool
        // boxing at the print/use site.
        if matches!(method, "all_truthy" | "any_truthy")
            && args.is_empty()
            && self.receiver_is_array(receiver, receiver_local_ty)
        {
            let receiver_reg = self.lower_expr(receiver)?;
            let runtime_fn = if method == "all_truthy" {
                "rt_array_all_truthy"
            } else {
                "rt_array_any_truthy"
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name(runtime_fn),
                    args: vec![receiver_reg],
                });
                dest
            });
        }

        // `arr.count_of(needle)` on an Array<T>: the interpreter
        // (interpreter_method/collections.rs "count_of") counts elements
        // equal to `needle`. `rt_array_count` (runtime/src/value/
        // collections.rs) already exists and compares via `rt_value_eq`,
        // which expects the `needle` argument in the SAME tag-boxed
        // representation as stored array elements — so `needle` needs the
        // identical int/float box-before-call step `arr.insert(idx, item)`
        // above already applies to its inserted item.
        if method == "count_of" && args.len() == 1 && self.receiver_is_array(receiver, receiver_local_ty) {
            let receiver_reg = self.lower_expr(receiver)?;
            let needle_reg_raw = self.lower_expr(&args[0])?;
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
            let needs_needle_float_boxing = matches!(needle_ty, TypeId::F32 | TypeId::F64);
            let needle_reg = if needle_ty == TypeId::U64 {
                self.box_u64_runtime_value(needle_reg_raw)?
            } else if needs_needle_int_boxing || needs_needle_float_boxing {
                let use_float = needs_needle_float_boxing;
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    if use_float {
                        block.instructions.push(MirInst::BoxFloat {
                            dest: boxed,
                            value: needle_reg_raw,
                        });
                    } else {
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: needle_reg_raw,
                        });
                    }
                    boxed
                })?
            } else {
                needle_reg_raw
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_array_count"),
                    args: vec![receiver_reg, needle_reg],
                });
                dest
            });
        }

        // rt_array_push returns bool, not a new pointer — no store-back needed.
        let _receiver_local_index: Option<usize> = None;

        let receiver_is_string = receiver.ty == TypeId::STRING || receiver_local_ty == Some(TypeId::STRING);
        if receiver_is_string {
            let unary_runtime = match (method, args.len()) {
                ("trim", 0) => Some("rt_string_trim"),
                ("lower" | "to_lower", 0) => Some("rt_string_to_lower"),
                ("upper" | "to_upper", 0) => Some("rt_string_to_upper"),
                _ => None,
            };
            if let Some(runtime_name) = unary_runtime {
                return self.lower_builtin_call_expr(runtime_name, std::slice::from_ref(receiver), TypeId::STRING);
            }

            // Preserve the canonical substring ABI: rt_slice(text, start, end, 1).
            // The one-bound form obtains `end` from rt_len; the two-bound form
            // forwards its explicit end. This is STRING-gated so a user type
            // declaring `substring` remains a direct user-method call.
            if method == "substring" && matches!(args.len(), 1 | 2) {
                let receiver_reg = self.lower_expr(receiver)?;
                let start_reg = self.lower_expr(&args[0])?;
                let end_reg = if args.len() == 2 {
                    self.lower_expr(&args[1])?
                } else {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        func.block_mut(current_block).unwrap().instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: crate::mir::effects::CallTarget::from_name("rt_len"),
                            args: vec![receiver_reg],
                        });
                        dest
                    })?
                };
                let step_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    func.block_mut(current_block)
                        .unwrap()
                        .instructions
                        .push(MirInst::ConstInt { dest, value: 1 });
                    dest
                })?;
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    func.block_mut(current_block).unwrap().instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::effects::CallTarget::from_name("rt_slice"),
                        args: vec![receiver_reg, start_reg, end_reg, step_reg],
                    });
                    dest
                });
            }
        }

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

        // `byte_at` is BYTE-indexed, unlike `char_code_at` which is
        // CHARACTER-indexed -- they deliberately diverge on non-ASCII text
        // (`"café,".byte_at(3)` is 195, the 0xC3 lead byte; `char_code_at(3)`
        // is 233 for 'é'). Must route to its own runtime primitive rather
        // than reusing `rt_string_char_code_at`, or byte-framing callers
        // (e.g. `browser_renderer_protocol.spl` scanning for byte 10/44)
        // desync on the first multi-byte codepoint.
        if method == "byte_at"
            && args.len() == 1
            && (receiver.ty == TypeId::STRING || receiver_local_ty == Some(TypeId::STRING))
        {
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_string_byte_at"),
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
        // `remove(index)` joins this family: it hands back an array SLOT verbatim
        // (the removed element), so it needs the identical UnboxInt/UnboxFloat
        // pairing. It differs only in taking ONE argument, hence the arity test
        // below is per-method rather than a blanket `args.is_empty()`.
        // Symptom when this is missing, measured on `[10,20,30].remove(1)` typed
        // `[i64]`: `160` instead of `20` — exactly 8x, the `v << 3` int tag still
        // attached. Typing `remove` in the HIR table alone is NOT sufficient; the
        // HIR type is what SELECTS this unbox, and without the unbox the tagged
        // word flows into an int-typed VReg.
        // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
        let is_slot_yielding_accessor =
            (args.is_empty() && matches!(method, "first" | "last" | "pop")) || (args.len() == 1 && method == "remove");
        if is_slot_yielding_accessor {
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
                    "remove" => "rt_array_remove",
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
                    // `remove` passes its index through; the others are nullary.
                    // NOTE the ABI difference: this calls `rt_array_remove`
                    // DIRECTLY, whose index parameter is a RAW native i64 — not
                    // the tag-boxed `RuntimeValue` that the erased-receiver
                    // `rt_collection_remove` dispatcher takes. So no shift is
                    // applied here, and none must be: `arg_regs[0]` is already
                    // an unboxed int in this typed path.
                    let call_args = if method == "remove" {
                        vec![receiver_reg, arg_regs[0]]
                    } else {
                        vec![receiver_reg]
                    };
                    return self.with_func(|func, current_block| {
                        let raw_result = func.new_vreg();
                        let unboxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(raw_result),
                            target: crate::mir::effects::CallTarget::from_name(rt_name),
                            args: call_args,
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
        // GATED ON AN ARRAY RECEIVER — same gate `index_of` uses just below.
        // `is_array_append_method` is a NAME test only, so without this gate a
        // user-defined `me append(...)`/`me push(...)` on a plain struct had its
        // FIRST integer argument tag-boxed (`v << 3`) at the call site while the
        // callee read it raw — every such call saw `value * 8`, silently, on the
        // JIT lane only (the tree-walk interpreter was unaffected).
        // See doc/08_tracking/bug/interp_me_method_first_param_times8_conditional_2026-06-29.md.
        if is_array_append_method && !args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
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
            let needs_push_float_boxing =
                matches!(push_arg_ty, TypeId::F32 | TypeId::F64) && !receiver_element_is_function;
            if push_arg_ty == TypeId::U64 {
                arg_regs[0] = self.box_u64_runtime_value(arg_regs[0])?;
            } else if needs_push_boxing || needs_push_float_boxing {
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
            if needle_ty == TypeId::U64 {
                arg_regs[0] = self.box_u64_runtime_value(arg_regs[0])?;
            } else if needs_needle_int_boxing || needs_needle_float_boxing {
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

        // Two-arg string `index_of(needle, start)`: byte-offset search from
        // `start` via the existing `rt_text_find(value, needle, start)`
        // runtime primitive (present in all three runtimes, previously
        // uncalled). This arity had NO lowering anywhere: the call fell
        // through to a static `str.index_of` symbol -> rt_function_not_found
        // at runtime, which printed an error but returned the tagged
        // SPECIAL_ERROR sentinel (27) with exit code 0 — a silent fail-open.
        // Semantics match one-arg `index_of` exactly: byte-indexed, raw i64
        // result, -1 for not-found; start < 0 clamps to 0, start past the end
        // returns -1 (empty needle returns min(start, len)). Gated off arrays
        // so `[T].index_of(v)` above is untouched; the receiver and needle
        // are tagged string handles like the one-arg `rt_index_of` route, and
        // `start` stays a raw i64 as `rt_text_find` expects.
        if method == "index_of" && args.len() == 2 && !self.receiver_is_array(receiver, receiver_local_ty) {
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: crate::mir::effects::CallTarget::from_name("rt_text_find"),
                    args: vec![receiver_reg, arg_regs[0], arg_regs[1]],
                });
                dest
            });
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
        // Signed `i64` has exactly the same problem in the same place: BoxInt
        // packs `(value << 3) | TAG_INT`, so i64::MAX boxed to -1 and 2^62 to 0
        // for `i64_val.to_string()` under the JIT while the tree-walking
        // interpreter rendered them correctly. Route it through the signed
        // bridge, mirroring u64. See
        // doc/08_tracking/bug/stage3_numeric_interpolation_slot_corruption_2026-08-13.md.
        if method == "to_string" || method == "to_text" || method == "str" {
            if receiver.ty == TypeId::U64 || receiver.ty == TypeId::I64 {
                let raw_fn = if receiver.ty == TypeId::U64 {
                    "rt_raw_u64_to_string"
                } else {
                    "rt_raw_i64_to_string"
                };
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::effects::CallTarget::from_name(raw_fn),
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
            } else if receiver.ty == TypeId::U64 {
                receiver_reg = self.box_u64_runtime_value(receiver_reg)?;
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
                let trait_lookup = self.find_trait_for_method_on_receiver(method, recv_type_name);
                // Duck-typed trait (no `impl Trait for ...` anywhere in the
                // unit, e.g. game2d's `App`/`GameBackend`): there is no vtable
                // to dispatch through, so the old lowering emitted the
                // DUCK_DISPATCH_UNSUPPORTED_SLOT sentinel and codegen turned
                // the call into a diagnostic + trap — the call simply did not
                // work (bugs jit_game2d_backend_method_dispatch_sigsegv_2026-07-02,
                // native_with_trait_impl_no_vtable_duck_trap_2026-07-28).
                //
                // The receiver is nevertheless a real object of some concrete
                // class that HAS the method, which is precisely the erased
                // (`Any`-typed receiver) shape the runtime already resolves by
                // name at the call site. So recover by lowering to a BARE-name
                // static method call instead of trapping. The name must be
                // bare: `func_name` was qualified with the receiver's static
                // type, which here is the TRAIT (`Backend.label`), and no such
                // function exists.
                //
                // Still-unsupported shapes deliberately left to the codegen
                // trap: any site that reaches `compile_method_call_virtual`
                // with the sentinel by another route. The trap stays
                // fail-closed and names the shape; it is not widened.
                // Native/AOT is NOT fixed by this: that backend has no erased
                // by-name method dispatch at all (an `Any`-typed receiver with
                // no trait involved fails there identically) — tracked in the
                // two bug rows above.
                if trait_lookup
                    .as_ref()
                    .is_some_and(|(slot, _, _)| *slot == crate::mir::DUCK_DISPATCH_UNSUPPORTED_SLOT)
                {
                    let bare = method.to_string();
                    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                        eprintln!(
                            "[MIR-METHOD-DISPATCH] '{}' on impl-less trait receiver: erased bare-name dispatch (was duck-dispatch trap)",
                            method
                        );
                    }
                    self.box_method_args_for_any_params(&bare, args, &mut arg_regs)?;
                    let dest = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::MethodCallStatic {
                            dest: Some(dest),
                            receiver: receiver_reg,
                            func_name: bare,
                            args: arg_regs,
                        });
                        dest
                    })?;
                    return Ok(dest);
                }
                if let Some((vtable_slot, param_types, return_type)) = trait_lookup {
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

#[cfg(test)]
mod enum_discriminant_abi_tests {
    use super::MirLowerer;
    use simple_runtime::value::hash_variant_discriminant;

    // Step (d), 2026-08-02. True-positive controls on the RUST SEED surface for
    // the bare-name enum collision campaign. Every earlier lane could only pin
    // the seed's behaviour by reading its source; these execute it.
    //
    // See doc/08_tracking/bug/enum_bare_name_collision_registry_2026-08-01.md.

    /// The seed wrapper must be the SAME function as the runtime's, not a copy
    /// of it. This is the whole point of step (d): the discriminant is a
    /// runtime ABI shared by `rt_option_some`/`rt_option_none`, the bytecode
    /// stream and the interpreter SFFI, so a second definition that drifted by
    /// one character would desynchronize compiled code from the runtime with no
    /// diagnostic at all.
    #[test]
    fn seed_wrapper_agrees_with_the_runtime_abi() {
        for name in ["Ok", "Err", "Some", "None", "Circle", "Bold"] {
            assert_eq!(
                MirLowerer::enum_variant_discriminant(name),
                hash_variant_discriminant(name) as i64,
                "seed wrapper diverged from the runtime ABI for variant {name}",
            );
        }
    }

    /// TRUE-POSITIVE CONTROL for the collision itself: the seed derives the
    /// discriminant from the variant NAME ALONE, with no enum identity, so two
    /// unrelated enums that both declare `Circle` collapse onto the identical
    /// discriminant BY CONSTRUCTION. This is measured here, not inferred from
    /// reading the source.
    ///
    /// This test is written to FAIL the moment the seed gains enum identity --
    /// which is the not-yet-done half of the reconciliation. Whoever makes that
    /// change must come here and replace this expectation deliberately, rather
    /// than discovering the ABI break in the field.
    #[test]
    fn seed_collapses_same_named_variants_of_different_enums() {
        // `Shape.Circle` and `Widget.Circle` are different enums. The seed
        // cannot tell them apart: it never sees an enum name.
        assert_eq!(
            MirLowerer::enum_variant_discriminant("Circle"),
            MirLowerer::enum_variant_discriminant("Circle"),
        );
        // ... while a genuinely different variant name does differ, so the
        // assertion above is not vacuously true of every input.
        assert_ne!(
            MirLowerer::enum_variant_discriminant("Circle"),
            MirLowerer::enum_variant_discriminant("Square"),
        );
    }

    /// TRUE-POSITIVE CONTROL for the numeric disagreement with the MIR `.spl`
    /// lowering, which uses the DECLARED ORDINAL (first variant = 0). The seed
    /// returns a 32-bit hash, so the two engines disagree numerically even for
    /// enums that do not collide at all. Pinned so the divergence cannot be
    /// quietly claimed to be resolved.
    #[test]
    fn seed_discriminant_is_a_hash_not_the_declared_ordinal() {
        // `Ok` is the FIRST variant of Result, so the MIR lowering assigns it
        // 0 and `Err` 1. The seed assigns neither.
        assert_ne!(MirLowerer::enum_variant_discriminant("Ok"), 0);
        assert_ne!(MirLowerer::enum_variant_discriminant("Err"), 1);
        // Well above any plausible ordinal, i.e. unmistakably a hash.
        assert!(MirLowerer::enum_variant_discriminant("Ok") > i64::from(u16::MAX));
    }
}

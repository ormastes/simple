//! Method call expression lowering (static and dynamic dispatch).

use super::lowering_core::{MirLowerResult, MirLowerer};
use super::lowering_di::builtin_type_name;
use crate::hir::{DispatchMode, HirExpr, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_method_call_expr(
        &mut self,
        receiver: &HirExpr,
        method: &str,
        args: &[HirExpr],
        dispatch: &DispatchMode,
    ) -> MirLowerResult<VReg> {
        // rt_array_push returns bool, not a new pointer — no store-back needed.
        let _receiver_local_index: Option<usize> = None;

        let mut receiver_reg = self.lower_expr(receiver)?;
        let mut arg_regs = Vec::new();
        for arg in args {
            arg_regs.push(self.lower_expr(arg)?);
        }

        // Box integer arguments for array .push() — matches IndexGet unbox at line 1236.
        // Without this, wrap_value (no-op) passes raw integers to rt_array_push,
        // but IndexGet + MIR UnboxInt expects tagged (val << 3) values.
        if method == "push" && !args.is_empty() {
            let push_arg_ty = args[0].ty;
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
            );
            if needs_push_boxing {
                let raw_arg = arg_regs[0];
                let boxed_arg = self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed,
                        value: raw_arg,
                    });
                    boxed
                })?;
                arg_regs[0] = boxed_arg;
            }
        }

        // Builtin primitive .to_string()/.str() routes to rt_to_string,
        // which expects a tagged RuntimeValue receiver rather than a
        // raw native scalar.
        if method == "to_string" || method == "str" {
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
        let receiver_local_ty: Option<TypeId> = self.recover_receiver_type(receiver);

        let func_name = if let Some(registry) = self.type_registry {
            if let Some(type_name) = registry.get_type_name(receiver.ty) {
                format!("{}.{}", type_name, method)
            } else if let Some(type_name) = builtin_type_name(receiver.ty) {
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
                } else if let Some(type_name) = builtin_type_name(local_ty) {
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

        let _receiver_ty = receiver.ty;
        match dispatch {
            DispatchMode::Dynamic => {
                // Try to find the method in a registered trait (vtable dispatch)
                if let Some((vtable_slot, param_types, return_type)) = self.find_trait_for_method(method) {
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

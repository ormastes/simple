// Closure and struct initialization helpers.

use cranelift_codegen::ir::{condcodes::IntCC, types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{FuncId, Linkage, Module};

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::shared::platform_call_conv;
use super::super::types_util::type_id_to_cranelift;
use super::helpers::{
    adapted_call, call_runtime_1, call_runtime_2, call_runtime_2_void, create_string_constant, get_vreg_or_default,
    indirect_call_with_result, inline_runtime_len_value,
};
use super::{InstrContext, InstrResult};

fn resolve_unique_module_qualified_func<M: Module>(ctx: &InstrContext<'_, M>, name: &str) -> Option<FuncId> {
    let sanitized = name.replace('.', "_dot_");
    let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
    let suffix = format!("__{}", tail);
    let mut ids: Vec<FuncId> = Vec::new();
    for (candidate, id) in ctx.func_ids.iter() {
        // Suffix match must respect the mangling boundary: a private helper
        // `_index_of` mangles to `<module>___index_of`, which ends_with
        // "__index_of" and used to false-positive-match method `index_of`
        // dynamic dispatch (SIGSEGV: test_config `.index_of` bound to
        // devhub__cmd_storage___index_of). Require the candidate's own tail
        // (after its LAST `__`) to equal the probed tail exactly.
        if candidate
            .strip_suffix(&suffix)
            .is_some_and(|prefix| !prefix.is_empty() && !prefix.ends_with('_'))
            && !ids.contains(id)
        {
            ids.push(*id);
        }
    }
    if ids.len() == 1 {
        ids.first().copied()
    } else {
        None
    }
}

fn resolve_unique_module_qualified_import<M: Module>(ctx: &InstrContext<'_, M>, name: &str) -> Option<String> {
    let sanitized = name.replace('.', "_dot_");
    let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
    let suffix = format!("__{}", tail);
    let mut names: Vec<String> = Vec::new();
    for candidate in ctx.use_map.values().chain(ctx.import_map.values()) {
        let candidate_sanitized = candidate.replace('.', "_dot_");
        // Same mangling-boundary rule as resolve_unique_module_qualified_func.
        if candidate_sanitized
            .strip_suffix(&suffix)
            .is_some_and(|prefix| !prefix.is_empty() && !prefix.ends_with('_'))
            && !names.iter().any(|n| n == candidate)
        {
            names.push(candidate.clone());
        }
    }
    if names.len() == 1 {
        names.first().cloned()
    } else {
        None
    }
}

fn erased_receiver_should_fall_through_ambiguous_method(receiver_ty: Option<TypeId>, method: &str) -> bool {
    matches!(receiver_ty, None | Some(TypeId::ANY)) && matches!(method, "to_string" | "to_text" | "str")
}

/// Default-off observability for the receiver-type-BLIND bare-method bind.
///
/// See `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`.
/// When a method call's receiver type was ERASED, the call reaches codegen as a
/// bare (dot-less) name and is bound to a `Type_dot_<method>` symbol by NAME
/// SUFFIX ALONE — the receiver type is never consulted. When exactly one such
/// symbol is linked into the module there is no ambiguity to report, so the
/// existing `[CODEGEN-AMBIGUOUS-METHOD]` diagnostic stays silent and a wrong
/// bind is only discovered later as a guest page fault (`starts_with`,
/// `ends_with`, `slice` were each found that way).
///
/// This reports every such bind so the class can be enumerated at compile time.
/// It is PURELY a report: it never changes which candidate is selected. Enable
/// with `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` (alongside the existing
/// `SIMPLE_DEBUG_METHOD_DISPATCH` knob).
fn erased_receiver_bind_diag_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("SIMPLE_DEBUG_ERASED_RECEIVER_BIND").is_ok())
}

fn report_erased_receiver_bind(
    caller: &str,
    method: &str,
    arg_count: usize,
    receiver_ty: Option<TypeId>,
    candidate: &str,
    candidate_count: usize,
) {
    if !erased_receiver_bind_diag_enabled() {
        return;
    }
    eprintln!(
        "[CODEGEN-ERASED-RECEIVER-BIND] in '{}' bare method '{}'({} args) receiver_ty={:?} bound by name-suffix alone to '{}' ({} candidate(s)) — receiver type is NOT checked; if the receiver is not that type this is a silent miscall",
        caller, method, arg_count, receiver_ty, candidate, candidate_count
    );
}

// `pub(crate)` so `mir/lower/lowering_expr_method.rs` can reuse the exact
// same builtin-collision name set for its own defense-in-depth guard (bug
// simpleos_native_build_bare_len_dynamic_dispatch_symbol_collision) instead
// of maintaining a second, potentially-drifting list.
pub(crate) fn is_bare_builtin_collection_method(method: &str, arg_count: usize) -> bool {
    matches!(
        (method, arg_count),
        ("get", 1)
            | ("has" | "contains" | "contains_key" | "has_key", 1)
            | ("remove", 1)
            | ("find", 1)
            // Text prefix/suffix tests. Same hazard as the collection idioms
            // above, and the one that page-faulted the SimpleOS WM guest
            // (2026-07-27): a bare `text.starts_with(prefix)` carries NO
            // receiver type at this point — `SIMPLE_DUMP_MIR` shows the MIR
            // for a text receiver and a ByteSpan receiver are byte-identical
            // (`MethodCallStatic { func_name: "starts_with" }`) — so the
            // cross-module `use_map`/`import_map` suffix scan in
            // `compile_method_call_static` binds it to the FIRST linked
            // `*.starts_with` it finds. Whenever `common.bytes.span` is
            // anywhere in the entry closure that is
            // `ByteSpan.starts_with`, which reads the text receiver as a
            // ByteSpan struct and dereferences garbage.
            // `rt_string_starts_with` / `rt_string_ends_with` tag-dispatch
            // safely on any value, so route bare calls there first.
            //
            // Scope note: this only fires for an ERASED receiver. A genuine
            // `span.starts_with(other_span)` on a typed ByteSpan (or
            // `path.starts_with(p)` on `fs_driver::Path`, the only other
            // in-tree instance method with this name/arity) lowers to the
            // qualified name "ByteSpan.starts_with", and the caller gates
            // this whole check on `!lookup_name.contains('.')`, so those
            // still resolve to their real method. `Matcher.starts_with` is
            // a `static fn` and is likewise always qualified.
            | ("starts_with" | "ends_with", 1)
            // Text/array slicing. Identical hazard to `starts_with` above and
            // found by the same reloc census (2026-07-28): a bare
            // `text.slice(a, b)` on an erased receiver was binding to
            // `ByteSpan.slice` whenever `common.bytes.span` was anywhere in
            // the entry closure, reading a text as a ByteSpan struct.
            // `rt_slice` tag-dispatches safely on any value and is already the
            // target reached for clean receivers, so route bare calls there
            // first.
            //
            // Arities are the ones `try_compile_builtin_method_call` actually
            // implements below: `start` is required, `end` and `step` are
            // optional (1..=3). Census of owned `.spl` sources: 178 one-arg,
            // 1922 two-arg, 1 three-arg call sites. Zero-arg is deliberately
            // excluded — a bare `.slice()` with no start is not a builtin
            // idiom and should keep falling through to normal resolution.
            | ("slice", 1 | 2 | 3)
            // `is_empty` is handled below (compiled as `rt_len(receiver) == 0`)
            // but was missing from this gate, so a bare (erased-receiver)
            // `.is_empty()` fell all the way through to suffix-based symbol
            // resolution instead of the safe tag-dispatching path.
            | ("len" | "length" | "keys" | "values" | "is_empty", 0)
            // Array mutators. Same hazard class as the collection idioms
            // above (doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md):
            // `push` is enumerated there as a confirmed erased-receiver THEFT
            // victim (`RingWindow.push` stole a bare `.push()` bind in the
            // `gui_entry_desktop` census) but was never added to this
            // allowlist. `pop` was not in that census, but a segfault traced
            // to `CoreLexer.scan_token`'s `self.indent_stack.pop()`
            // (doc/08_tracking/bug/self_hosted_array_pop_segfault_lex_command_2026-07-29.md)
            // is consistent with the same class, and `rt_array_pop` already
            // tag-dispatches safely on any value (see the `"pop" =>
            // "rt_array_pop"` arm below), so routing bare `.pop()` there
            // first is the same defensive move already made for `len` et al.
            // `clear` is deliberately excluded: the erased-receiver-bind
            // census in the bug doc classified `clear` binds as legitimate
            // erased-field dispatch (e.g. `self.backend.clear()`), not theft
            // — adding it here would break those.
            | ("pop", 0)
            | ("push" | "append", 1)
            // Text/array search. Enumerated as a confirmed erased-receiver
            // THEFT in the census (8 binds, all stolen by
            // `dbfs_engine.txn.TxnStepSequence.index_of`) but never added
            // here. Reproduced minimally 2026-08-01 under the seed JIT:
            //
            //   struct Foo:  (impl Foo: fn index_of(self, needle: text) -> i64: return 999)
            //   val e = "hello world".lower()   # result type is erased to ANY
            //   e.index_of("world")             # -> 999, not 6
            //
            // `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` on that fixture reports
            // `receiver_ty=Some(TypeId(14))` (= `TypeId::ANY`) bound by
            // name-suffix alone to `Foo.index_of`.
            //
            // `rt_index_of` tag-dispatches: it tries `rt_array_index_of`
            // (whose `as_typed_ptr!` fails closed with -1 on a non-array) and
            // then `rt_string_find`, so it is safe on any receiver value.
            //
            // Scope note: arity 1 only. A user `index_of(a, b)` (or a 0-arg
            // one) still falls through to normal name resolution, and a typed
            // receiver emits a qualified `Type.index_of` which the caller's
            // `!lookup_name.contains('.')` gate excludes.
            | ("index_of", 1)
    )
}

pub(crate) fn compile_closure_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    func_name: &str,
    closure_size: usize,
    capture_offsets: &[u32],
    captures: &[VReg],
) {
    let allocation_size = closure_size.max(16);
    let size_val = builder.ins().iconst(types::I64, allocation_size as i64);
    let closure_ptr = call_runtime_1(ctx, builder, "rt_alloc", size_val);

    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let fn_addr = builder.ins().func_addr(types::I64, func_ref);
        builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
    } else {
        // Cross-module closure: resolve via use_map → import_map
        let mut resolved_name = ctx
            .use_map
            .get(func_name)
            .or_else(|| ctx.import_map.get(func_name))
            .map(|s| s.as_str());

        // Try: TypeName__method → typename_method (factory/constructor convention)
        let mut dunder_storage;
        if resolved_name.is_none() {
            if let Some((type_part, method_part)) = func_name.split_once("__") {
                if type_part.chars().next().is_some_and(|c| c.is_uppercase()) {
                    dunder_storage = format!("{}_{}", type_part.to_lowercase(), method_part);
                    resolved_name = ctx
                        .use_map
                        .get(&dunder_storage)
                        .or_else(|| ctx.import_map.get(&dunder_storage))
                        .map(|s| s.as_str());
                }
            }
        }

        if let Some(resolved) = resolved_name {
            let resolved = if resolved.contains('.') {
                std::borrow::Cow::Owned(resolved.replace('.', "_dot_"))
            } else {
                std::borrow::Cow::Borrowed(resolved)
            };
            // Declare as import with a generic i64 → i64 signature (closure body)
            let call_conv = platform_call_conv();
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64)); // closure pointer
            sig.returns.push(AbiParam::new(types::I64));
            // Use cached func_id if available, otherwise declare and cache
            let fid_result = if let Some(&existing) = ctx.func_ids.get(resolved.as_ref()) {
                Ok(existing)
            } else {
                let result = ctx.module.declare_function(&resolved, Linkage::Import, &sig);
                if let Ok(id) = &result {
                    ctx.func_ids.insert(resolved.to_string(), *id);
                }
                result
            };
            match fid_result {
                Ok(fid) => {
                    let func_ref = ctx.module.declare_func_in_func(fid, builder.func);
                    let fn_addr = builder.ins().func_addr(types::I64, func_ref);
                    builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
                }
                Err(_) => {
                    let null = builder.ins().iconst(types::I64, 0);
                    builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
                }
            }
        } else {
            eprintln!(
                "[WARN] ClosureCreate: function '{}' not found in func_ids ({} entries), storing NULL",
                func_name,
                ctx.func_ids.len()
            );
            let null = builder.ins().iconst(types::I64, 0);
            builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
        }
    }

    if closure_size < 16 {
        let null_marker = builder.ins().iconst(types::I64, 0);
        builder.ins().store(MemFlags::new(), null_marker, closure_ptr, 8);
    }

    for (i, offset) in capture_offsets.iter().enumerate() {
        let cap_val = get_vreg_or_default(ctx, builder, &captures[i]);
        builder
            .ins()
            .store(MemFlags::new(), cap_val, closure_ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, closure_ptr);
}

pub(crate) fn compile_indirect_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    callee: VReg,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let closure_ptr = get_vreg_or_default(ctx, builder, &callee);
    let fn_ptr = builder.ins().load(types::I64, MemFlags::new(), closure_ptr, 0);

    let mut sig = Signature::new(platform_call_conv());
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![closure_ptr];
    for arg in args {
        call_args.push(get_vreg_or_default(ctx, builder, arg));
    }

    indirect_call_with_result(ctx, builder, sig_ref, fn_ptr, &call_args, dest);
}

#[allow(clippy::too_many_arguments)] // reason: struct init requires all field context
pub(crate) fn compile_struct_init<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    struct_size: usize,
    field_offsets: &[u32],
    field_types: &[TypeId],
    field_values: &[VReg],
    vtable_data_id: Option<cranelift_module::DataId>,
) {
    let size_val = builder.ins().iconst(types::I64, struct_size as i64);
    let ptr = call_runtime_1(ctx, builder, "rt_alloc", size_val);

    // Write vtable pointer at offset 0 if this struct implements a trait
    if let Some(data_id) = vtable_data_id {
        let vtable_global = ctx.module.declare_data_in_func(data_id, builder.func);
        let vtable_ptr = builder.ins().global_value(types::I64, vtable_global);
        builder.ins().store(MemFlags::new(), vtable_ptr, ptr, 0);
    }

    for (i, (offset, field_type)) in field_offsets.iter().zip(field_types.iter()).enumerate() {
        // Handle case where field_values has fewer elements than field_offsets/types
        let field_val = if i < field_values.len() {
            if let Some(&val) = ctx.vreg_values.get(&field_values[i]) {
                val
            } else {
                // VReg not found - use default value (0 for pointers/integers)
                builder.ins().iconst(types::I64, 0)
            }
        } else {
            // More fields than values - use default 0
            builder.ins().iconst(types::I64, 0)
        };
        let storage_val = widen_struct_field_value(builder, field_val, *field_type);
        builder.ins().store(MemFlags::new(), storage_val, ptr, *offset as i32);
    }

    // Struct values use the same tagged heap-object ABI as arrays/strings once
    // they can flow through generic containers. Field access masks the tag.
    let heap_tag = builder.ins().iconst(types::I64, 1);
    let tagged_ptr = builder.ins().bor(ptr, heap_tag);
    ctx.vreg_values.insert(dest, tagged_ptr);
}

/// Lane F1 / S5 — duplicate an aggregate's storage (see `MirInst::AggregateCopy`).
///
/// The struct ABI here is the one `compile_struct_init` above establishes: a
/// value is `rt_alloc`'d block pointer with the heap tag in bit 0. A plain
/// `Copy` of that register aliases the block; this duplicates it.
///
/// Memory safety is branch-free by construction. A nil aggregate carries a
/// null payload pointer, and loading through it would fault, so the load
/// address is `select(src == 0, fresh, src)` — a nil source degenerates into
/// a self-copy of the fresh (uninitialised) block rather than a segfault.
/// That is deliberately not "correct nil handling"; it is the guarantee that
/// introducing this instruction cannot turn a wrong answer into a crash.
pub(crate) fn compile_aggregate_copy<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    src: VReg,
    byte_size: u32,
    deep_fields: &[crate::mir::AggregateFieldCopy],
) {
    let Some(&src_tagged) = ctx.vreg_values.get(&src) else {
        // Undefined source: behave exactly as `Copy` does — define nothing.
        return;
    };
    // Only the I64 tagged-pointer representation is a known aggregate handle.
    // Anything else is not the ABI this instruction is defined over, so alias
    // rather than fabricate a copy of something whose layout is unknown.
    if builder.func.dfg.value_type(src_tagged) != types::I64 {
        ctx.vreg_values.insert(dest, src_tagged);
        return;
    }

    let tagged = emit_aggregate_block_copy(ctx, builder, src_tagged, byte_size, deep_fields);
    ctx.vreg_values.insert(dest, tagged);
}

/// Recursive worker for `compile_aggregate_copy`: copy one aggregate block,
/// then deep-copy the field slots the descriptor names. Recursion depth is
/// the STATIC descriptor tree's depth (built with a cycle guard at lowering),
/// so termination is unconditional. Branch-free like the shallow copy: a slot
/// that does not currently hold a live tagged heap handle (nil, or a raw
/// scalar left by an untyped path) keeps its original word via `select`.
fn emit_aggregate_block_copy<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    src_tagged: cranelift_codegen::ir::Value,
    byte_size: u32,
    deep_fields: &[crate::mir::AggregateFieldCopy],
) -> cranelift_codegen::ir::Value {
    // Round up to whole 8-byte words and never allocate zero.
    let words = byte_size.div_ceil(8).max(1);
    let alloc_bytes = i64::from(words) * 8;

    let size_val = builder.ins().iconst(types::I64, alloc_bytes);
    let new_ptr = call_runtime_1(ctx, builder, "rt_alloc", size_val);

    let tag_mask = builder.ins().iconst(types::I64, 7);
    let untag_mask = builder.ins().iconst(types::I64, !7i64);
    let src_ptr = builder.ins().band(src_tagged, untag_mask);
    let zero = builder.ins().iconst(types::I64, 0);
    let one = builder.ins().iconst(types::I64, 1);
    let src_tag = builder.ins().band(src_tagged, tag_mask);
    let src_is_heap = builder.ins().icmp(IntCC::Equal, src_tag, one);
    let src_nonnull = builder.ins().icmp(IntCC::NotEqual, src_ptr, zero);
    let src_is_valid = builder.ins().band(src_is_heap, src_nonnull);
    let load_ptr = builder.ins().select(src_is_valid, src_ptr, new_ptr);

    for w in 0..words {
        let off = (w * 8) as i32;
        let word = builder.ins().load(types::I64, MemFlags::new(), load_ptr, off);
        let word = builder.ins().select(src_is_valid, word, zero);
        builder.ins().store(MemFlags::new(), word, new_ptr, off);
    }

    for field in deep_fields {
        let off = (field.word_index * 8) as i32;
        if field.word_index >= words {
            continue; // descriptor out of range — fail closed, keep shallow
        }
        let word = builder.ins().load(types::I64, MemFlags::new(), new_ptr, off);
        let inner = emit_aggregate_block_copy(ctx, builder, word, field.byte_size, &field.nested);
        // Replace only a live tagged heap handle; nil (0) and non-handle
        // words keep their original value (the inner alloc is then unused).
        let tag_bit = builder.ins().band(word, tag_mask);
        let is_tagged = builder.ins().icmp(IntCC::Equal, tag_bit, one);
        let payload = builder.ins().band(word, untag_mask);
        let nonnull = builder.ins().icmp(IntCC::NotEqual, payload, zero);
        let is_handle = builder.ins().band(is_tagged, nonnull);
        let result = builder.ins().select(is_handle, inner, word);
        builder.ins().store(MemFlags::new(), result, new_ptr, off);
    }

    let heap_tag = builder.ins().iconst(types::I64, 1);
    builder.ins().bor(new_ptr, heap_tag)
}

fn widen_struct_field_value(
    builder: &mut FunctionBuilder,
    value: cranelift_codegen::ir::Value,
    field_type: TypeId,
) -> cranelift_codegen::ir::Value {
    let actual_ty = builder.func.dfg.value_type(value);
    // Float fields: convert to the field's DECLARED width, because
    // `compile_field_get` loads each slot with `type_id_to_cranelift(field_type)`.
    // Storing an f64 into an `f32` slot and then loading 4 bytes back is a bit
    // TRUNCATION, not a numeric conversion: `2.5f64` is `0x4004000000000000`,
    // whose low 32 bits are zero, so `s.a` read back as `0.0`; `0.1f64` read
    // back as `-1.588e-23`. Demote/promote so store width == load width.
    if actual_ty.is_float() {
        let storage_ty = type_id_to_cranelift(field_type);
        if storage_ty.is_float() && storage_ty != actual_ty {
            return if storage_ty.bits() < actual_ty.bits() {
                builder.ins().fdemote(storage_ty, value)
            } else {
                builder.ins().fpromote(storage_ty, value)
            };
        }
        return value;
    }
    if actual_ty == types::I64 || !actual_ty.is_int() {
        return value;
    }
    let storage_ty = type_id_to_cranelift(field_type);
    let signed = matches!(field_type, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
    if storage_ty.is_int() && actual_ty.bits() < types::I64.bits() {
        if signed {
            builder.ins().sextend(types::I64, value)
        } else {
            builder.ins().uextend(types::I64, value)
        }
    } else if storage_ty.is_int() && actual_ty.bits() > types::I64.bits() {
        builder.ins().ireduce(types::I64, value)
    } else {
        value
    }
}

pub(crate) fn compile_method_call_static<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    func_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    let lookup_name_storage = if func_name.contains("_dot_") {
        Some(func_name.replace("_dot_", "."))
    } else {
        None
    };
    let lookup_name = lookup_name_storage.as_deref().unwrap_or(func_name);
    if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
        eprintln!(
            "[CODEGEN-METHOD-STATIC] in '{}' func_name='{}' args={}",
            ctx.func.name,
            func_name,
            args.len()
        );
    }
    let ctype_method_imported = ctx.use_map.iter().chain(ctx.import_map.iter()).any(|(raw, mangled)| {
        (raw.contains("ctype") || mangled.contains("ctype"))
            && (raw.ends_with(lookup_name) || mangled.ends_with(lookup_name))
    });
    if ctype_method_imported {
        if super::calls::compile_inline_ctype_call(
            ctx,
            builder,
            dest,
            &format!("ctype.{lookup_name}"),
            lookup_name,
            args,
        )? {
            return Ok(());
        }
    }
    if lookup_name.ends_with(".char_code_at") {
        if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, "char_code_at", args)? {
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
            }
            return Ok(());
        }
    }
    // ROOT FIX (bug #62, 2026-07-02): receiver-type-aware dispatch for the
    // builtin Dict/Array/String idioms whose static type was ERASED.
    //
    // `Dict<K,V>` (and `Set`) resolve to `TypeId::ANY` in the HIR type
    // resolver (src/hir/lower/type_resolver.rs:426), so a call like
    // `scope.symbols.get(name)` / `scope.symbols.contains(name)` reaches codegen
    // as a BARE (dot-less) `MethodCallStatic` — the receiver carries no type to
    // qualify the name. The name-suffix resolution below (lines ~454+) is
    // receiver-type-BLIND: it binds a bare method to any unique `Type_dot_<m>`
    // symbol linked into the module. That silently miscalls a builtin dict op
    // onto a same-named USER struct method (last-write / shortest-name wins) and
    // segfaults the self-hosted binary — e.g. `scope.symbols.get(name)` bound to
    // `SymbolTable.get(id: SymbolId?)` (bare-name collision on `get`),
    // `manifest.entries.has(path)` → `SuffixRegistry.has` (2026-06-10),
    // `line.len()` → `ListIter.len` (2026-06-11), `sendfile_pending.get(fd)` →
    // `StaticCompressionCache.get` (2026-06-17).
    //
    // The correct dispatch is by RECEIVER TYPE: for a bare (type-erased) receiver
    // these idioms are the builtin collection operations, which the runtime
    // implements with TAG-DISPATCHED functions (rt_index_get / rt_contains /
    // rt_dict_remove / rt_len) that inspect the receiver's runtime tag and are
    // safe on any value (nil/miss for non-collections). Route them to the builtin
    // BEFORE any name-based resolution so a builtin always wins over a same-named
    // user method here. Receivers whose static type IS known emit a qualified
    // "Type.<method>" name and never take this path (`lookup_name.contains('.')`
    // is false only for erased receivers). Arity is gated so a genuine user
    // method with a different signature (e.g. `get()` / `get(a, b)`) still falls
    // through to normal resolution when the builtin does not apply.
    let bare_builtin_collection =
        !lookup_name.contains('.') && is_bare_builtin_collection_method(lookup_name, args.len());
    if bare_builtin_collection {
        let recv_ty = ctx.vreg_types.get(&receiver).copied();
        if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, lookup_name, args)? {
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
                if let Some(rt) = builtin_method_result_type(lookup_name, recv_ty) {
                    ctx.vreg_types.insert(*d, rt);
                }
            }
            return Ok(());
        }
    }
    let receiver_ty = ctx.vreg_types.get(&receiver).copied();
    let allow_qualified_builtin = matches!(
        receiver_ty,
        Some(
            TypeId::BOOL
                | TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
                | TypeId::F32
                | TypeId::F64
                | TypeId::STRING
                | TypeId::CHAR
        )
    ) || matches!(
        lookup_name.rsplit_once('.'),
        Some((
            "Array" | "array" | "Dict" | "dict" | "Tuple" | "tuple" | "str" | "String" | "string",
            _
        ))
    );
    let prefer_builtin_first = lookup_name.contains('.') && allow_qualified_builtin;

    // Only run builtin lowering first for qualified builtin scalar/string
    // receivers like `i64.to_float`. For bare names like `bitmap.get(...)`,
    // prefer resolving an actual method implementation before falling back to
    // collection builtins such as `rt_index_get`.
    if prefer_builtin_first {
        if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, lookup_name, args)? {
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
                if let Some(rt) = builtin_method_result_type(lookup_name, receiver_ty) {
                    ctx.vreg_types.insert(*d, rt);
                }
            }
            // NOTE: Do NOT store the push result back to the receiver variable.
            // rt_array_push returns bool (success/failure), NOT a new array pointer.
            // The array is mutated in-place; the pointer stays valid.
            // Storing the bool (1=true) back would corrupt the array variable,
            // causing segfaults on subsequent array access.
            return Ok(());
        }
    }

    // Try to find the function - check multiple patterns
    // 1. Exact match (func_name or sanitized variant with _dot_)
    // 2. Type-qualified name (ClassName.method) - search for functions ending with ".func_name"
    let sanitized_name = lookup_name.replace('.', "_dot_");

    // Self-recursion guard: when a free function `fn foo(s: T, ...)` dispatches
    // `s.foo(...)` as a bare MethodCallStatic with func_name == "foo", the
    // exact-match `func_ids.get("foo")` returns the enclosing function itself,
    // producing infinite recursion at runtime.  Skip any exact-match candidate
    // that resolves to the currently-compiling function.
    //
    // Mangled keys use the form "module__name" or raw "name"; ctx.func.name
    // holds either the raw short name or a dot-qualified "Type.method" form.
    let current_fn_name_ex: &str = ctx.func.name.as_str();
    let current_fn_sanitized_ex = current_fn_name_ex.replace('.', "_dot_");
    let is_self = |name: &str| -> bool {
        if lookup_name.contains('.') {
            return false;
        }
        let tail_dot = format!("__{}", current_fn_name_ex);
        let tail_san = format!("__{}", current_fn_sanitized_ex);
        name == current_fn_name_ex
            || name == current_fn_sanitized_ex.as_str()
            || name.ends_with(&tail_dot)
            || name.ends_with(&tail_san)
    };

    let mut method_resolution_error: Option<String> = None;
    let func_id = resolve_unique_module_qualified_func(ctx, lookup_name)
        .or_else(|| resolve_unique_module_qualified_func(ctx, &sanitized_name))
        .or_else(|| ctx
        .func_ids
        .get(lookup_name)
        .filter(|_| !is_self(lookup_name))
        .copied())
        .or_else(|| {
            ctx.func_ids
                .get(&sanitized_name)
                .filter(|_| !is_self(&sanitized_name))
                .copied()
        })
        .or_else(|| {
            if !lookup_name.contains('.') {
                return None;
            }
            let mapped = ctx
                .use_map
                .get(lookup_name)
                .or_else(|| ctx.import_map.get(lookup_name))
                .or_else(|| ctx.use_map.get(&sanitized_name))
                .or_else(|| ctx.import_map.get(&sanitized_name))?;
            ctx.func_ids
                .get(mapped.as_str())
                .or_else(|| ctx.func_ids.get(&mapped.replace('.', "_dot_")))
                .filter(|_| !is_self(mapped))
                .copied()
        })
        .or_else(|| {
            // Search for a function ending with ".func_name" or "_dot_func_name"
            // If func_name is already qualified (contains '.'), extract the method part only
            let method_part = lookup_name.rsplit('.').next().unwrap_or(lookup_name);

            // Bare `.has(...)` is overwhelmingly the builtin Dict/Set/Array
            // membership idiom (583 uses in src/compiler alone). Binding it
            // by name-suffix to whatever unique `Type_dot_has` method happens
            // to be linked in (e.g. os.kernel CapabilitySet.has in the stage4
            // CLI closure) miscompiles every dict lookup and segfaulted
            // interpret_file in the self-hosted binary (2026-06-10). Skip
            // name-based binding for bare `has`; the builtin fallback lowers
            // it to rt_contains, which tag-dispatches safely at runtime.
            if !lookup_name.contains('.') && method_part == "has" {
                return None;
            }
            // Same policy for bare `len`/`length` (see the rt_len routing
            // above): never bind by name-suffix to an arbitrary linked
            // `Type_dot_len`.
            if !lookup_name.contains('.') && (method_part == "len" || method_part == "length") {
                return None;
            }

            let dot_suffix = format!(".{}", method_part);
            let underscore_suffix = format!("_dot_{}", method_part);

            // If we have a type qualifier (e.g., "VirtioGpuDriver.init_from_grant"),
            // prefer functions whose full path contains the type name
            let type_qualifier = if lookup_name.contains('.') {
                lookup_name.split('.').next()
            } else {
                None
            };

            // Exclude the currently-compiled function from candidates so that
            // bare `method(...)` inside `Type.method` (or `self.field.method`
            // where `self.field` has unknown type) does not resolve to the
            // enclosing method itself. The "pick shortest candidate" fallback
            // would otherwise produce infinite recursion for delegating
            // wrappers like
            //   fn draw_rect_filled(self, ...):
            //     self.backend.draw_rect_filled(...)
            // where `self.backend` has no concrete type at the call site.
            //
            // `ctx.func.name` is the short form "Type.method" or a bare
            // function name; `func_ids` keys are mangled
            // ("module__Type_dot_method"). A candidate is considered the
            // current function if its mangled name equals or ends with the
            // sanitized short form.
            let current_fn_name: &str = ctx.func.name.as_str();
            let current_fn_sanitized = current_fn_name.replace('.', "_dot_");
            let current_fn_tail_dot = format!("__{}", current_fn_name);
            let current_fn_tail_sanitized = format!("__{}", current_fn_sanitized);
            let candidates: Vec<_> = ctx
                .func_ids
                .iter()
                .filter(|(k, _)| k.ends_with(&dot_suffix) || k.ends_with(&underscore_suffix))
                .filter(|(k, _)| {
                    let ks = k.as_str();
                    ks != current_fn_name
                        && ks != current_fn_sanitized
                        && !ks.ends_with(&current_fn_tail_dot)
                        && !ks.ends_with(&current_fn_tail_sanitized)
                })
                .collect();

            if let Some(tq) = type_qualifier {
                // Prefer candidate whose name contains the type qualifier
                let tq_dot = format!("{}_dot_", tq);
                let tq_dunder = format!("__{}", tq);
                if let Some((_, &v)) = candidates
                    .iter()
                    .find(|(k, _)| k.contains(&tq_dot) || k.contains(&tq_dunder) || k.contains(tq))
                {
                    return Some(v);
                }
                // No candidate matches the type qualifier — return None so
                // that the cross-module use_map/import_map path runs below.
                // Without this, the "pick shortest" fallback at the bottom
                // would match a candidate from an unrelated type (e.g. the
                // enclosing class's own method of the same name), causing
                // infinite recursion for `self.field.method()` calls where
                // `self.field`'s concrete type is not in the current
                // compilation unit's func_ids.
                return None;
            }

            if candidates.len() > 1 {
                let method_dot = format!("_dot_{}", method_part);
                for (cand_name, &cand_id) in &candidates {
                    // Extract type name from candidate: "mod__Type_dot_method" → "Type"
                    if let Some(dot_pos) = cand_name.rfind(&method_dot) {
                        let prefix = &cand_name[..dot_pos];
                        // Get the type name (last segment after __)
                        let type_name = prefix.rsplit("__").next().unwrap_or(prefix);
                        if ctx.use_map.contains_key(type_name) {
                            return Some(cand_id);
                        }
                    }
                }
                // Also check import_map for "TypeName.method" where TypeName is in use_map
                for (raw, mangled) in ctx.import_map.iter() {
                    if raw.ends_with(&format!(".{}", method_part)) && raw.len() > method_part.len() + 1 {
                        let type_part = &raw[..raw.len() - method_part.len() - 1];
                        if ctx.use_map.contains_key(type_part) {
                            // Find the candidate matching this mangled name
                            if let Some((_, &v)) = candidates.iter().find(|(k, _)| k.as_str() == mangled.as_str()) {
                                return Some(v);
                            }
                        }
                    }
                }
            }

            // Fallback: pick shortest name (most specific).
            //
            // SAFETY NOTE (Agent δ, 2026-04-13): when `lookup_name` is a bare
            // unqualified method name (no dot) and `candidates.len() > 1`,
            // "pick shortest" silently dispatches one class's method call to
            // another class's method of the same name — this is what caused
            // `DesktopShell.init()` to be emitted as a call to
            // `Ps2Keyboard.init()` (or `Ps2Mouse.init()` depending on module
            // order) on the x86_64 baremetal desktop lane. See Agent V's
            // 2026-04-13 `launcher_init()`-in-`new()` workaround. When this
            // ambiguity hits with no type hint we now emit a compile-time
            // diagnostic (loud, via `[CODEGEN-AMBIGUOUS-METHOD]`) and return
            // None so the outer path falls back to a cross-module use_map
            // lookup (or `rt_method_not_found` if that also fails) instead
            // of silently picking a random wrong target. For qualified lookups
            // (with type_qualifier) we keep the existing behaviour — the
            // dot-prefix already picked the right candidate above, and the
            // tail here is only a one-candidate fallthrough.
            // 2026-04-18: same FuncId can appear under multiple keys (raw
            // `Type.method` + mangled `module__Type_dot_method` both inserted
            // by declare_functions in common_backend.rs:425-429 — intentional
            // dual-registration for local-call resolution). When all surviving
            // candidates point to the same FuncId, treat as one.
            // See doc/05_design/compiler_rfc_ufcs.md.
            let unique_ids: std::collections::HashSet<_> =
                candidates.iter().map(|(_, id)| **id).collect();
            if type_qualifier.is_none() && candidates.len() > 1 && unique_ids.len() == 1 {
                report_erased_receiver_bind(
                    &ctx.func.name,
                    method_part,
                    args.len(),
                    receiver_ty,
                    candidates[0].0.as_str(),
                    candidates.len(),
                );
                return Some(*candidates[0].1);
            }
            if type_qualifier.is_none()
                && candidates.len() > 1
                && matches!(
                    method_part,
                    "unwrap" | "unwrap_or" | "unwrap_err" | "expect" | "is_some" | "is_none" | "is_ok" | "is_err"
                )
            {
                return None;
            }
            if type_qualifier.is_none() && candidates.len() > 1 {
                if erased_receiver_should_fall_through_ambiguous_method(receiver_ty, method_part) {
                    return None;
                }
                let cand_names: Vec<&str> = candidates.iter().map(|(k, _)| k.as_str()).collect();
                let message = format!(
                    "[CODEGEN-AMBIGUOUS-METHOD] in '{}' bare method '{}' has {} candidates: [{}] — refusing to pick shortest (would silently miscall). Qualify the receiver type (e.g. `var x: Type = ...`) or import only one matching method.",
                    ctx.func.name,
                    method_part,
                    candidates.len(),
                    cand_names.join(", ")
                );
                eprintln!("{message}");
                method_resolution_error = Some(message);
                return None;
            }
            // Reaching here means `type_qualifier` is None (a qualified lookup
            // returned above) and `candidates.len() <= 1` (the >1 arms all
            // returned). So this is EXACTLY the single-candidate
            // erased-receiver bind that produced the known thefts, and it is
            // silent today. Report it (default-off) without changing the pick.
            let picked = candidates.iter().min_by_key(|(k, _)| k.len());
            if let Some((cand_name, _)) = picked {
                report_erased_receiver_bind(
                    &ctx.func.name,
                    method_part,
                    args.len(),
                    receiver_ty,
                    cand_name.as_str(),
                    candidates.len(),
                );
            }
            picked.map(|(_, v)| **v)
        });

    if let Some(error) = method_resolution_error {
        return Err(error);
    }

    if let Some(func_id) = func_id {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let sig_ref = builder.func.dfg.ext_funcs[func_ref].signature;
        let sig_params = builder.func.dfg.signatures[sig_ref].params.len();
        let mut call_args = if sig_params == args.len() {
            vec![]
        } else {
            vec![get_vreg_or_default(ctx, builder, &receiver)]
        };
        for arg in args {
            call_args.push(get_vreg_or_default(ctx, builder, arg));
        }
        let call_args = super::calls::adapt_args_to_signature(builder, func_ref, call_args);
        let call = adapted_call(builder, func_ref, &call_args);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            } else {
                let null = builder.ins().iconst(types::I64, 0);
                ctx.vreg_values.insert(*d, null);
            }
        }
    } else {
        // Cross-module method: resolve via use_map → import_map
        // First try exact match, then check for "TypeName.method" qualified
        // entries in use_map (prefers imported types over alphabetical import_map)
        let mut resolved_name = ctx.use_map.get(func_name).map(|s| s.as_str());
        // Check use_map for "TypeName.func_name" entries (from imported impl methods)
        if resolved_name.is_none() {
            let method_suffix = format!(".{}", func_name);
            for (raw, mangled) in ctx.use_map.iter() {
                if raw.ends_with(&method_suffix) && raw.len() > lookup_name.len() + 1 {
                    resolved_name = Some(mangled.as_str());
                    break;
                }
            }
        }
        // Also check import_map for qualified entries where type is imported
        if resolved_name.is_none() {
            let method_suffix = format!(".{}", lookup_name);
            for (raw, mangled) in ctx.import_map.iter() {
                if raw.ends_with(&method_suffix) && raw.len() > lookup_name.len() + 1 {
                    let type_part = &raw[..raw.len() - method_suffix.len()];
                    if ctx.use_map.contains_key(type_part) {
                        resolved_name = Some(mangled.as_str());
                        break;
                    }
                }
            }
        }
        // Final fallback: import_map bare name (may pick wrong overload)
        if resolved_name.is_none()
            && !matches!(
                lookup_name,
                "unwrap" | "unwrap_or" | "unwrap_err" | "expect" | "is_some" | "is_none" | "is_ok" | "is_err"
            )
        {
            resolved_name = ctx.import_map.get(lookup_name).map(|s| s.as_str());
        }

        // If not found and func_name contains '.', try additional name variants.
        // Prefer qualified/type-specific spellings before the bare method name.
        let mut type_prefixed_storage;
        let mut dunder_storage;
        if resolved_name.is_none() {
            if let Some(dot_pos) = lookup_name.rfind('.') {
                let type_name = &lookup_name[..dot_pos];
                let method = &lookup_name[dot_pos + 1..];

                // Try: Type__method (double underscore variant)
                dunder_storage = format!("{}__{}", type_name, method);
                resolved_name = ctx
                    .use_map
                    .get(&dunder_storage)
                    .or_else(|| ctx.import_map.get(&dunder_storage))
                    .map(|s| s.as_str());

                // Try: Type_dot_method (sanitized dot variant, used in cross-compiled targets)
                if resolved_name.is_none() {
                    let dot_storage = format!("{}_dot_{}", type_name, method);
                    resolved_name = ctx
                        .use_map
                        .get(&dot_storage)
                        .or_else(|| ctx.import_map.get(&dot_storage))
                        .map(|s| s.as_str());
                    // dot_storage is consumed by the resolved_name reference above
                }

                // Try: lowercase_type_method (Simple convention)
                if resolved_name.is_none() {
                    type_prefixed_storage = format!("{}_{}", type_name.to_lowercase(), method);
                    resolved_name = ctx
                        .use_map
                        .get(&type_prefixed_storage)
                        .or_else(|| ctx.import_map.get(&type_prefixed_storage))
                        .map(|s| s.as_str());
                }

                // Last resort: bare method name
                if resolved_name.is_none() {
                    resolved_name = ctx
                        .use_map
                        .get(method)
                        .or_else(|| ctx.import_map.get(method))
                        .map(|s| s.as_str());
                }
            }
        }

        // Try: TypeName__method → typename_method (factory/constructor convention)
        // e.g., TreeSitter__new → treesitter_new
        if resolved_name.is_none() {
            if let Some((type_part, method_part)) = func_name.split_once("__") {
                if type_part.chars().next().is_some_and(|c| c.is_uppercase()) {
                    type_prefixed_storage = format!("{}_{}", type_part.to_lowercase(), method_part);
                    resolved_name = ctx
                        .use_map
                        .get(&type_prefixed_storage)
                        .or_else(|| ctx.import_map.get(&type_prefixed_storage))
                        .map(|s| s.as_str());
                }
            }
        }

        let suffix_resolved_storage;
        if resolved_name.is_none() {
            suffix_resolved_storage = resolve_unique_module_qualified_import(ctx, lookup_name);
            resolved_name = suffix_resolved_storage.as_deref();
        }

        if let Some(resolved) = resolved_name {
            let resolved = if resolved.contains('.') {
                std::borrow::Cow::Owned(resolved.replace('.', "_dot_"))
            } else {
                std::borrow::Cow::Borrowed(resolved)
            };
            let is_free_fn = ctx
                .fn_arities
                .get(resolved.as_ref())
                .map(|&arity| arity == args.len())
                .unwrap_or(false);
            let fid = resolve_unique_module_qualified_func(ctx, resolved.as_ref())
                .or_else(|| ctx.func_ids.get(resolved.as_ref()).copied())
                .unwrap_or_else(|| {
                    let call_conv = platform_call_conv();
                    let mut sig = Signature::new(call_conv);
                    let param_count = if is_free_fn { args.len() } else { args.len() + 1 };
                    for _ in 0..param_count {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.returns.push(AbiParam::new(types::I64));
                    let id = ctx
                        .module
                        .declare_function(&resolved, Linkage::Import, &sig)
                        .or_else(|_| {
                            let mut sig2 = Signature::new(call_conv);
                            let alt_count = if is_free_fn { args.len() + 1 } else { args.len() };
                            for _ in 0..alt_count {
                                sig2.params.push(AbiParam::new(types::I64));
                            }
                            sig2.returns.push(AbiParam::new(types::I64));
                            ctx.module.declare_function(&resolved, Linkage::Import, &sig2)
                        })
                        .unwrap_or_else(|_| match ctx.module.get_name(&resolved) {
                            Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                            _ => ctx.runtime_funcs["rt_function_not_found"],
                        });
                    ctx.func_ids.insert(resolved.to_string(), id);
                    id
                });
            let fref = ctx.module.declare_func_in_func(fid, builder.func);
            let mut call_args = if is_free_fn {
                vec![]
            } else {
                vec![get_vreg_or_default(ctx, builder, &receiver)]
            };
            for a in args {
                call_args.push(get_vreg_or_default(ctx, builder, a));
            }
            let call_args = super::calls::adapt_args_to_signature(builder, fref, call_args);
            let call = adapted_call(builder, fref, &call_args);
            if let Some(d) = dest {
                let results = builder.inst_results(call);
                if !results.is_empty() {
                    ctx.vreg_values.insert(*d, results[0]);
                }
            }
        } else if let Some((type_name, "new")) = lookup_name.rsplit_once('.') {
            if args.is_empty() && type_name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                if let Some(d) = dest {
                    ctx.vreg_values.insert(*d, get_vreg_or_default(ctx, builder, &receiver));
                }
            } else {
                let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;
                let result = call_runtime_2(ctx, builder, "rt_function_not_found", name_ptr, name_len);
                if let Some(d) = dest {
                    ctx.vreg_values.insert(*d, result);
                }
            }
        } else {
            let recv_ty = ctx.vreg_types.get(&receiver).copied();
            if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, lookup_name, args)? {
                if let Some(d) = dest {
                    ctx.vreg_values.insert(*d, result);
                    if let Some(rt) = builtin_method_result_type(lookup_name, recv_ty) {
                        ctx.vreg_types.insert(*d, rt);
                    }
                }
                return Ok(());
            }
            let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;
            let result = call_runtime_2(ctx, builder, "rt_function_not_found", name_ptr, name_len);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erased_receiver_ambiguity_falls_through() {
        assert!(erased_receiver_should_fall_through_ambiguous_method(None, "to_string"));
        assert!(erased_receiver_should_fall_through_ambiguous_method(
            Some(TypeId::ANY),
            "to_string"
        ));
        assert!(!erased_receiver_should_fall_through_ambiguous_method(
            Some(TypeId::ANY),
            "push"
        ));
        assert!(!erased_receiver_should_fall_through_ambiguous_method(
            Some(TypeId::I64),
            "to_string"
        ));
    }

    #[test]
    fn erased_dict_views_use_builtin_dispatch() {
        assert!(is_bare_builtin_collection_method("keys", 0));
        assert!(is_bare_builtin_collection_method("values", 0));
        assert!(!is_bare_builtin_collection_method("keys", 1));
    }

    /// A bare `text.starts_with(prefix)` must reach `rt_string_starts_with`
    /// before any name/use_map resolution, or it binds to whatever
    /// `Type.starts_with` (e.g. `ByteSpan.starts_with`) happens to be linked
    /// into the entry closure and dereferences the text as that struct.
    #[test]
    fn erased_text_prefix_suffix_use_builtin_dispatch() {
        assert!(is_bare_builtin_collection_method("starts_with", 1));
        assert!(is_bare_builtin_collection_method("ends_with", 1));
        // Arity-gated: a differently-shaped user method still resolves normally.
        assert!(!is_bare_builtin_collection_method("starts_with", 0));
        assert!(!is_bare_builtin_collection_method("starts_with", 2));
        assert!(!is_bare_builtin_collection_method("ends_with", 2));
    }

    /// Same defect class as `starts_with`: a bare `text.slice(a, b)` was
    /// binding to `ByteSpan.slice` (reloc census on `mod_0.o`, 2026-07-28)
    /// instead of the tag-dispatching `rt_slice`. Arities are the ones
    /// `try_compile_builtin_method_call` implements: start required, end and
    /// step optional.
    #[test]
    fn erased_slice_uses_builtin_dispatch() {
        assert!(is_bare_builtin_collection_method("slice", 1));
        assert!(is_bare_builtin_collection_method("slice", 2));
        assert!(is_bare_builtin_collection_method("slice", 3));
        // Arity-gated at both ends: no-start and over-long forms still resolve
        // through normal name resolution.
        assert!(!is_bare_builtin_collection_method("slice", 0));
        assert!(!is_bare_builtin_collection_method("slice", 4));
    }

    /// Same defect class again, enumerated in the 2026-07-28 census (8 stolen
    /// binds) and reproduced minimally 2026-08-01: an erased `text` receiver
    /// bound `.index_of(needle)` to a same-module `Foo.index_of` and returned
    /// that method's value instead of the match position.
    #[test]
    fn erased_index_of_uses_builtin_dispatch() {
        assert!(is_bare_builtin_collection_method("index_of", 1));
        // Arity-gated: only the 1-arg builtin idiom is captured, so a user
        // `index_of()` / `index_of(a, b)` still resolves normally.
        assert!(!is_bare_builtin_collection_method("index_of", 0));
        assert!(!is_bare_builtin_collection_method("index_of", 2));
    }

    /// The two Cranelift bare-name dispatch tables must not send a
    /// receiver-polymorphic method to a receiver-SPECIFIC helper, and must not
    /// contain a SECOND arm for a name already matched earlier — Rust `match`
    /// is first-match-wins, so a second arm is dead code that reads like a
    /// working array route. `calls.rs` carried exactly that for `find`.
    ///
    /// Each check pairs "the dead mapping is gone" with "the live mapping is
    /// present", so deleting an arm cannot satisfy the test.
    ///
    /// Self-matching is impossible by construction rather than by excluding a
    /// region: every needle contains `"` characters, which in THIS file's source
    /// are written `\"`, so the assertion text never contains the needle it
    /// searches for. (Region-excluding would not work here anyway —
    /// `calls.rs` declares its `mod tests` near the TOP of the file, above the
    /// dispatch table being checked.)
    #[test]
    fn cranelift_bare_name_tables_have_no_dead_or_receiver_specific_find_reverse() {
        let calls = include_str!("calls.rs");
        let closures = include_str!("closures_structs.rs");

        // --- calls.rs -------------------------------------------------------
        assert!(
            calls.contains("\"find\" => Some(\"rt_find\")"),
            "calls.rs must route the bare `find` to the polymorphic rt_find"
        );
        assert!(
            !calls.contains("\"find\" => Some(\"rt_array_find\")"),
            "the dead second `find` arm must not come back — it is unreachable"
        );
        assert!(
            !calls.contains("\"find\" | \"find_str\" => Some(\"rt_string_find\")"),
            "the bare `find` must not be folded back into the text-only arm"
        );
        assert!(
            calls.contains("\"find_str\" => Some(\"rt_string_find\")"),
            "`find_str` is text-only and must keep its direct route"
        );
        // `reverse` vs `rev`/`reversed` are DIFFERENT contracts, not synonyms.
        // These assertions previously demanded `"reverse" => rt_reverse`, i.e.
        // they PINNED the divergence: `interpreter_method/mod.rs` lists
        // `"reverse"` in `MUTATING_METHODS` and omits `"rev"`/`"reversed"`, so
        // the interpreter rebinds the receiver for `reverse` alone, while the
        // copying helper left it untouched. Measured: `a.reverse()` leaves
        // `a == [3,2,1]`, `a.rev()` leaves `a == [1,2,3]`.
        assert!(
            calls.contains("\"reverse\" => Some(\"rt_reverse_mut\")"),
            "calls.rs must route the MUTATING `reverse` to rt_reverse_mut"
        );
        assert!(
            !calls.contains("\"reverse\" => Some(\"rt_reverse\")"),
            "the copying rt_reverse does not rebind the receiver; that is the rev/reversed contract"
        );
        assert!(
            !calls.contains("\"reverse\" => Some(\"rt_array_reverse\")"),
            "rt_array_reverse returns a bool and is absent from runtime_native.c"
        );
        // The pure spellings must NOT follow `reverse` — the whole point of the
        // split. This is the true-positive control for this pair.
        assert!(
            calls.contains("\"rev\" | \"reversed\" => Some(\"rt_reverse\")"),
            "rev/reversed must keep the copying rt_reverse"
        );

        // --- closures_structs.rs -------------------------------------------
        assert!(
            closures.contains("\"find\" => \"rt_find\""),
            "bare `find` must reach rt_find"
        );
        assert!(
            !closures.contains("\"find\" => \"rt_string_find\""),
            "the text-only route made every array find answer -1"
        );
        assert!(
            closures.contains("\"reverse\" => \"rt_reverse_mut\""),
            "bare mutating `reverse` must reach rt_reverse_mut"
        );
        assert!(!closures.contains("\"reverse\" => \"rt_reverse\""));
        assert!(!closures.contains("\"reverse\" => \"rt_array_reverse\""));
        assert!(
            closures.contains("\"rev\" | \"reversed\" => \"rt_reverse\""),
            "rev/reversed must keep the copying rt_reverse"
        );

        // --- sort ------------------------------------------------------------
        // `sort` carried the identical divergence `reverse` had: the bare-name
        // tables routed it to `rt_array_sort`, which sorts IN PLACE, returns a
        // bool, applies to every receiver, and does not exist in
        // runtime_native.c at all. It used to sit below as this test's
        // "true-positive control" — which is exactly how a known-wrong mapping
        // gets PINNED by the test meant to protect the family. `rt_sort` copies,
        // matching the interpreter's `arr.to_vec()` -> `Value::array(new_arr)`.
        assert!(
            calls.contains("\"sort\" => Some(\"rt_sort\")"),
            "calls.rs must route `sort` to the copying rt_sort"
        );
        assert!(
            !calls.contains("\"sort\" => Some(\"rt_array_sort\")"),
            "rt_array_sort mutates in place and returns a bool"
        );
        assert!(
            closures.contains("\"sort\" => \"rt_sort\""),
            "bare `sort` must reach rt_sort"
        );
        assert!(!closures.contains("\"sort\" => \"rt_array_sort\""));

        // --- push / pop / clear ----------------------------------------------
        // The same divergence, on the last three type-blind mutator names. The
        // array-only helpers fail CLOSED on a text receiver, so text answered
        // `0` (push), nil (pop) and the UNCLEARED receiver (clear) here while
        // the interpreter returned a new text. Measured on `var t = "abc"`
        // before the split, JIT / interpreter:
        //   push  -> `0`     / `"abcd"`
        //   pop   -> `nil`   / `Option::Some("c")`
        //   clear -> `"abc"` / `""`
        // `rt_push`/`rt_pop`/`rt_clear` dispatch on the receiver; the array
        // contract is byte-for-byte what it was.
        assert!(
            calls.contains("\"push\" => Some(\"rt_push\")"),
            "calls.rs must route `push` to the receiver-dispatched rt_push"
        );
        assert!(
            !calls.contains("\"push\" => Some(\"rt_array_push\")"),
            "rt_array_push fails closed to `false` on a text receiver"
        );
        assert!(calls.contains("\"pop\" => Some(\"rt_pop\")"));
        assert!(!calls.contains("\"pop\" => Some(\"rt_array_pop\")"));
        assert!(calls.contains("\"clear\" => Some(\"rt_clear\")"));
        assert!(!calls.contains("\"clear\" => Some(\"rt_array_clear\")"));
        assert!(
            closures.contains("\"push\" | \"append\" => \"rt_push\""),
            "bare `push`/`append` must reach rt_push"
        );
        assert!(!closures.contains("\"push\" | \"append\" => \"rt_array_push\""));
        assert!(closures.contains("\"pop\" => \"rt_pop\""));
        assert!(!closures.contains("\"pop\" => \"rt_array_pop\""));
        assert!(closures.contains("\"clear\" => \"rt_clear\""));
        assert!(!closures.contains("\"clear\" => \"rt_array_clear\""));

        // True-positive control: receiver-SPECIFIC methods must STAY specific,
        // so this cannot be satisfied by a table that renamed everything.
        // `first`/`filter` take an array receiver in both tables and have no
        // text counterpart, so unlike `sort` they are genuinely specific.
        assert!(calls.contains("\"first\" => Some(\"rt_array_first\")"));
        assert!(closures.contains("\"filter\" => \"rt_array_filter\""));
    }
}

/// `true` for the integer code-point-to-character builtin, in either the bare
/// (`chr`) or the receiver-qualified (`i64.chr`) spelling the caller's
/// `lookup_name` can carry. The receiver-type prefix is restricted to integer
/// spellings so a user-defined `SomeStruct.chr` still resolves normally.
fn is_int_chr_method(name: &str) -> bool {
    let (owner, method) = match name.rsplit_once('.') {
        Some((owner, method)) => (Some(owner), method),
        None => (None, name),
    };
    if !matches!(method, "chr" | "to_char") {
        return false;
    }
    match owner {
        None => true,
        Some(owner) => matches!(
            owner,
            "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "uint" | "Int" | "isize" | "usize"
        ),
    }
}

/// Static result type of a builtin method, when it is knowable from the method
/// name plus the (possibly unknown) receiver type.
///
/// This exists because the builtin call sites below only ever recorded the
/// result VALUE (`ctx.vreg_values`) and never its TYPE (`ctx.vreg_types`). A
/// *directly chained* builtin — `arg.substring(10).to_int()` — therefore handed
/// the next method a receiver vreg with no recorded type, and the numeric-cast
/// block further down defaults a missing type to `TypeId::I64`
/// (`unwrap_or(TypeId::I64)`). `to_int` then skipped the `from_ty ==
/// TypeId::STRING` branch that routes to `rt_string_to_int` and fell into the
/// generic raw-register conversion, which returned the intermediate text's HEAP
/// POINTER as a "successful" integer — no error, no warning, exit 0, and a
/// value that changed between runs. Binding the intermediate to a typed `val`
/// first made it correct, because that path does record the type.
///
/// Deliberately conservative: it answers `None` unless the result type is
/// certain, so a wrong entry can never make a previously-correct call worse.
/// Text-returning entries require a known-STRING receiver for the same reason —
/// `slice` is shared with arrays, where the result is an array, not text.
fn builtin_method_result_type(method: &str, receiver_ty: Option<TypeId>) -> Option<TypeId> {
    let method = method.rsplit('.').next().unwrap_or(method);
    match method {
        // Length/position queries are raw i64 on every receiver.
        "len" | "length" | "char_code_at" | "index_of" | "find_index" => Some(TypeId::I64),
        // Predicates are bool on every receiver.
        "is_empty" | "contains" | "starts_with" | "ends_with" => Some(TypeId::BOOL),
        // Text-in/text-out. `slice`/`substring` are shared with array receivers,
        // so they are only classified when the receiver is known to be text.
        "substring" | "slice" | "trim" | "trim_start" | "trim_end" | "to_upper" | "to_uppercase" | "to_lower"
        | "to_lowercase" | "char_at" | "replace" | "concat" => {
            if receiver_ty == Some(TypeId::STRING) {
                Some(TypeId::STRING)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Try to compile a builtin method call (String, Array methods)
/// Returns Some(result_value) if the method was handled, None otherwise
fn try_compile_builtin_method_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    receiver: VReg,
    method: &str,
    args: &[VReg],
) -> InstrResult<Option<cranelift_codegen::ir::Value>> {
    let receiver_val = get_vreg_or_default(ctx, builder, &receiver);

    // Extract plain method name from qualified name (e.g., "text.len" -> "len")
    let method = method.rsplit('.').next().unwrap_or(method);

    // Handle slice specially since it has optional parameters
    if method == "slice" || method == "substring" {
        let Some(&slice_id) = ctx.runtime_funcs.get("rt_slice") else {
            return Ok(None);
        };
        let slice_ref = ctx.module.declare_func_in_func(slice_id, builder.func);

        // start argument (required)
        let start = if !args.is_empty() {
            get_vreg_or_default(ctx, builder, &args[0])
        } else {
            builder.ins().iconst(types::I64, 0)
        };

        // end argument (optional, defaults to collection length)
        let end = if args.len() > 1 {
            get_vreg_or_default(ctx, builder, &args[1])
        } else {
            // Default to collection length
            inline_runtime_len_value(builder, receiver_val)
        };

        // step argument (optional, defaults to 1)
        let step = if args.len() > 2 {
            get_vreg_or_default(ctx, builder, &args[2])
        } else {
            builder.ins().iconst(types::I64, 1)
        };

        let call = adapted_call(builder, slice_ref, &[receiver_val, start, end, step]);
        return Ok(Some(builder.inst_results(call)[0]));
    }

    // is_empty: compile as rt_len(receiver) == 0
    if method == "is_empty" {
        let len_val = inline_runtime_len_value(builder, receiver_val);
        let zero = builder.ins().iconst(types::I64, 0);
        let result = builder
            .ins()
            .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, len_val, zero);
        return Ok(Some(result));
    }

    // Numeric type conversion methods must produce a real native cast so later
    // boxing preserves the intended width and signedness.
    //
    // The cast names are matched EXACTLY. This guard used to be a prefix test
    // (`starts_with("to_u") || starts_with("to_i") || starts_with("to_f")`),
    // which also captured every non-cast method sharing those three prefixes --
    // `to_upper`, `to_uppercase`, `to_include`, `to_index`, `to_int_or`,
    // `to_utf8`, `to_iterable`, `to_id`, `to_import`, `to_unix_timestamp`,
    // `to_feature_string` -- and then dropped them on the match's wildcard arm,
    // which returned the receiver UNCHANGED. Every such call was therefore a
    // silent no-op under the JIT that still exited 0: `"hello".to_upper()`
    // evaluated to `"hello"` where the interpreter correctly returned `"HELLO"`.
    // Names that are not numeric casts must fall through to the normal
    // builtin/user-method resolution below, where e.g. `to_upper` is already
    // mapped to `rt_string_to_upper`.
    let numeric_cast_target = match method {
        "to_u8" => Some(TypeId::U8),
        "to_u16" => Some(TypeId::U16),
        "to_u32" => Some(TypeId::U32),
        "to_u64" => Some(TypeId::U64),
        "to_i8" => Some(TypeId::I8),
        "to_i16" => Some(TypeId::I16),
        "to_i32" => Some(TypeId::I32),
        "to_i64" | "to_int" => Some(TypeId::I64),
        "to_f32" => Some(TypeId::F32),
        "to_f64" | "to_float" => Some(TypeId::F64),
        _ => None,
    };
    if let Some(to_ty) = numeric_cast_target {
        let from_ty = ctx.vreg_types.get(&receiver).copied().unwrap_or(TypeId::I64);

        let to_is_int = matches!(
            to_ty,
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
        );
        if from_ty == TypeId::STRING && to_is_int {
            let func_id = if let Some(&fid) = ctx.runtime_funcs.get("rt_string_to_int") {
                fid
            } else {
                let mut sig = cranelift_codegen::ir::Signature::new(platform_call_conv());
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                let fid = ctx
                    .module
                    .declare_function("rt_string_to_int", cranelift_module::Linkage::Import, &sig)
                    .map_err(|e| e.to_string())?;
                ctx.func_ids.insert("rt_string_to_int".to_string(), fid);
                fid
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let parsed = builder.inst_results(call)[0];
            let converted = match to_ty {
                TypeId::U8 | TypeId::I8 => builder.ins().ireduce(types::I8, parsed),
                TypeId::U16 | TypeId::I16 => builder.ins().ireduce(types::I16, parsed),
                TypeId::U32 | TypeId::I32 => builder.ins().ireduce(types::I32, parsed),
                TypeId::U64 | TypeId::I64 => parsed,
                _ => parsed,
            };
            return Ok(Some(converted));
        }

        // Mirrors the STRING->int branch just above: without this, a STRING
        // receiver falls into the generic from/to conversion below, which
        // assumes `receiver_val` is already a raw numeric register and emits
        // `fcvt_from_uint` on the STRING'S TAGGED POINTER — reinterpreting a
        // heap address as an integer-to-float conversion instead of parsing
        // the string. `rt_string_to_float` returns a heap-boxed RuntimeValue
        // (like `rt_value_float`), so unbox it via `rt_value_as_float` to get
        // a genuine raw f64 register, matching how `rt_string_to_int` above
        // already returns a raw native i64. See float print bug (lane
        // FLOATBOX, 2026-07-29): `s.to_float()` printed/arithmetic'd a
        // pointer-derived garbage float that changed between runs.
        if from_ty == TypeId::STRING && matches!(to_ty, TypeId::F32 | TypeId::F64) {
            let func_id = if let Some(&fid) = ctx.runtime_funcs.get("rt_string_to_float") {
                fid
            } else {
                let mut sig = cranelift_codegen::ir::Signature::new(platform_call_conv());
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                let fid = ctx
                    .module
                    .declare_function("rt_string_to_float", cranelift_module::Linkage::Import, &sig)
                    .map_err(|e| e.to_string())?;
                ctx.func_ids.insert("rt_string_to_float".to_string(), fid);
                fid
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let boxed = builder.inst_results(call)[0];
            let unbox_func_id = if let Some(&fid) = ctx.runtime_funcs.get("rt_value_as_float") {
                fid
            } else {
                let mut sig = cranelift_codegen::ir::Signature::new(platform_call_conv());
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::F64));
                let fid = ctx
                    .module
                    .declare_function("rt_value_as_float", cranelift_module::Linkage::Import, &sig)
                    .map_err(|e| e.to_string())?;
                ctx.func_ids.insert("rt_value_as_float".to_string(), fid);
                fid
            };
            let unbox_func_ref = ctx.module.declare_func_in_func(unbox_func_id, builder.func);
            let unbox_call = adapted_call(builder, unbox_func_ref, &[boxed]);
            let raw_f64 = builder.inst_results(unbox_call)[0];
            let converted = if to_ty == TypeId::F32 {
                builder.ins().fdemote(types::F32, raw_f64)
            } else {
                raw_f64
            };
            return Ok(Some(converted));
        }

        let converted = if from_ty == to_ty {
            receiver_val
        } else {
            let src_ty = builder.func.dfg.value_type(receiver_val);
            let from_signed = matches!(from_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
            // Defensive: MIR's `from_ty` is sometimes wrong when an
            // expression chain returned a float but the result vreg kept its
            // declared int type (e.g. `(a.to_f32() * opacity).to_u32()` in
            // browser_engine `_apply_opacity`, where `a.to_f32() * opacity`
            // is f32 at runtime but vreg_types still records the surrounding
            // u32). Without this branch we'd dispatch a bare `ireduce.i32`
            // on an f32 value and the verifier rejects it. Honor the
            // cranelift value type so float→int casts always go through
            // `fcvt_to_{sint,uint}`.
            let actual_is_float = src_ty == types::F32 || src_ty == types::F64;
            let to_is_int = matches!(
                to_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            );
            if actual_is_float && to_is_int {
                let to_signed = matches!(to_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
                let widened = if to_signed {
                    builder.ins().fcvt_to_sint(types::I64, receiver_val)
                } else {
                    builder.ins().fcvt_to_uint(types::I64, receiver_val)
                };
                match to_ty {
                    TypeId::U8 | TypeId::I8 => builder.ins().ireduce(types::I8, widened),
                    TypeId::U16 | TypeId::I16 => builder.ins().ireduce(types::I16, widened),
                    TypeId::U32 | TypeId::I32 => builder.ins().ireduce(types::I32, widened),
                    _ => widened, // I64/U64
                }
            } else if actual_is_float && matches!(to_ty, TypeId::F32 | TypeId::F64) {
                // Float→float: promote/demote between F32 and F64.
                if src_ty == types::F32 && to_ty == TypeId::F64 {
                    builder.ins().fpromote(types::F64, receiver_val)
                } else if src_ty == types::F64 && to_ty == TypeId::F32 {
                    builder.ins().fdemote(types::F32, receiver_val)
                } else {
                    receiver_val
                }
            } else {
                match to_ty {
                    TypeId::U8 | TypeId::I8 => builder.ins().ireduce(types::I8, receiver_val),
                    TypeId::U16 | TypeId::I16 => builder.ins().ireduce(types::I16, receiver_val),
                    TypeId::U32 | TypeId::I32 => builder.ins().ireduce(types::I32, receiver_val),
                    TypeId::U64 | TypeId::I64 => match src_ty {
                        types::I8 | types::I16 | types::I32 => {
                            if from_signed {
                                builder.ins().sextend(types::I64, receiver_val)
                            } else {
                                builder.ins().uextend(types::I64, receiver_val)
                            }
                        }
                        _ => receiver_val,
                    },
                    TypeId::F32 | TypeId::F64 => {
                        let float_val = if from_signed {
                            builder.ins().fcvt_from_sint(types::F64, receiver_val)
                        } else {
                            builder.ins().fcvt_from_uint(types::F64, receiver_val)
                        };
                        if to_ty == TypeId::F32 {
                            builder.ins().fdemote(types::F32, float_val)
                        } else {
                            float_val
                        }
                    }
                    _ => receiver_val,
                }
            }
        };
        return Ok(Some(converted));
    }

    // FR-COMPILER-012: scalar float intrinsics via MethodCallStatic path
    if matches!(method, "sqrt" | "abs" | "floor" | "ceil" | "round") {
        let src_ty = builder.func.dfg.value_type(receiver_val);
        let is_float = src_ty == types::F32 || src_ty == types::F64;
        if is_float {
            let result_val = match method {
                "sqrt" => builder.ins().sqrt(receiver_val),
                "abs" => builder.ins().fabs(receiver_val),
                "floor" => builder.ins().floor(receiver_val),
                "ceil" => builder.ins().ceil(receiver_val),
                "round" => builder.ins().nearest(receiver_val),
                _ => unreachable!(),
            };
            return Ok(Some(result_val));
        } else if method == "sqrt" {
            // Integer sqrt: convert to f64, compute sqrt
            let f64_val = builder.ins().fcvt_from_sint(types::F64, receiver_val);
            let result_val = builder.ins().sqrt(f64_val);
            return Ok(Some(result_val));
        } else if method == "abs" {
            // Integer abs: native Cranelift `iabs` instruction.
            let result_val = builder.ins().iabs(receiver_val);
            return Ok(Some(result_val));
        }
        // floor/ceil/round have no integer meaning; fall through.
    }
    // `trunc` is also a first-class Cranelift float instruction (round toward
    // zero) — same treatment as the block above.
    if method == "trunc" {
        let src_ty = builder.func.dfg.value_type(receiver_val);
        if src_ty == types::F32 || src_ty == types::F64 {
            let result_val = builder.ins().trunc(receiver_val);
            return Ok(Some(result_val));
        }
    }
    // The remaining float math methods (`sin`/`cos`/`tan`/.../`pow`/`max`/
    // `min`) have no native Cranelift instruction; route them to the same
    // `rt_math_*` runtime symbols the free-function forms already use
    // (`mir/lower/lowering_expr_builtin.rs::lower_libm_math`), declared with
    // the real `f64 -> f64` ABI. This is the actual dispatch site for method
    // calls lowered via `MirInst::MethodCallStatic` (this function), which is
    // a separate table from the `MirInst::BuiltinMethod` one in
    // `codegen/instr/methods.rs::compile_builtin_method`.
    // See doc/08_tracking/bug/float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md.
    {
        let unary_rt_name = match method {
            "sin" => Some("rt_math_sin"),
            "cos" => Some("rt_math_cos"),
            "tan" => Some("rt_math_tan"),
            "asin" => Some("rt_math_asin"),
            "acos" => Some("rt_math_acos"),
            "atan" => Some("rt_math_atan"),
            "sinh" => Some("rt_math_sinh"),
            "cosh" => Some("rt_math_cosh"),
            "tanh" => Some("rt_math_tanh"),
            "exp" => Some("rt_math_exp"),
            "ln" => Some("rt_math_log"),
            "log2" => Some("rt_math_log2"),
            "log10" => Some("rt_math_log10"),
            "cbrt" => Some("rt_math_cbrt"),
            _ => None,
        };
        let binary_rt_name = match method {
            "pow" | "powf" => Some("rt_math_pow"),
            "max" => Some("rt_math_max"),
            "min" => Some("rt_math_min"),
            "atan2" => Some("rt_math_atan2"),
            "hypot" => Some("rt_math_hypot"),
            _ => None,
        };
        let src_ty = builder.func.dfg.value_type(receiver_val);
        let is_float = src_ty == types::F32 || src_ty == types::F64;
        if is_float {
            if let Some(rt_name) = unary_rt_name {
                let recv_f64 = if src_ty == types::F32 {
                    builder.ins().fpromote(types::F64, receiver_val)
                } else {
                    receiver_val
                };
                let mut result_val = call_runtime_1(ctx, builder, rt_name, recv_f64);
                if src_ty == types::F32 {
                    result_val = builder.ins().fdemote(types::F32, result_val);
                }
                return Ok(Some(result_val));
            }
            if let Some(rt_name) = binary_rt_name {
                if args.is_empty() {
                    return Ok(None);
                }
                let arg_val = get_vreg_or_default(ctx, builder, &args[0]);
                let arg_ty = builder.func.dfg.value_type(arg_val);
                let recv_f64 = if src_ty == types::F32 {
                    builder.ins().fpromote(types::F64, receiver_val)
                } else {
                    receiver_val
                };
                let arg_f64 = if arg_ty == types::F32 {
                    builder.ins().fpromote(types::F64, arg_val)
                } else if arg_ty != types::F64 {
                    // Integer arg (e.g. `f.max(5)`): convert to float.
                    builder.ins().fcvt_from_sint(types::F64, arg_val)
                } else {
                    arg_val
                };
                let mut result_val = call_runtime_2(ctx, builder, rt_name, recv_f64, arg_f64);
                if src_ty == types::F32 {
                    result_val = builder.ins().fdemote(types::F32, result_val);
                }
                return Ok(Some(result_val));
            }
        }
    }

    // Map method names to runtime functions
    let runtime_func = match method {
        // String methods
        "starts_with" => "rt_string_starts_with",
        "ends_with" => "rt_string_ends_with",
        "concat" => "rt_string_concat",
        "contains" => "rt_contains",
        "char_at" => "rt_string_char_at",
        // See calls.rs: `at` is receiver-dispatched via `rt_at` so an array
        // receiver yields a real `Option` instead of a silent `nil`.
        "at" => "rt_at",
        "char_code_at" => "rt_string_char_code_at",
        "byte_at" => "rt_string_byte_at",
        "hash" => "rt_hash_text",
        // Array methods.
        //
        // Receiver-polymorphic (see calls.rs): the array-only helpers fail
        // closed on a text receiver, so a text `push`/`pop`/`clear` produced
        // `0` / nil / the UNCLEARED receiver here while the interpreter
        // returned a new text. `rt_push`/`rt_pop`/`rt_clear` dispatch on the
        // receiver and leave the array contract unchanged.
        "push" | "append" => "rt_push",
        "pop" => "rt_pop",
        "clear" => "rt_clear",
        // Bulk in-place span copy — JIT counterpart of the interpreter's
        // `arr.write_span(src, dst_off, src_off, count)` mutating method
        // (rt_array_write_span mutates the receiver heap array in place and
        // returns the count written). Array-only name; no other receiver
        // type defines it.
        "write_span" => "rt_array_write_span",
        // Generic collection methods (work on String, Array, Tuple, Dict)
        "len" | "length" => "rt_len",
        // Result/Option methods.
        //
        // This is the bare/dynamic-dispatch fallback used when the receiver's
        // static type is erased (`Any`) or is a flat-nullable `T?` (HIR
        // `Pointer { inner: T }`, which stores its payload directly rather
        // than as a boxed `Option::Some` enum object). `rt_enum_payload`
        // returns tagged-nil (`RuntimeValue` bit pattern `3`, see
        // `create_enum_value` in codegen/instr/result.rs) whenever the
        // receiver is not a genuine heap-tagged `Enum` object — which is
        // always true for flat-nullable locals holding a present value.
        // Callers here then either pass that nil straight to `print` (empty
        // output instead of the value) or, when the statically-inferred
        // return type is an integer, wrap it in another `BoxInt`, which
        // re-tags the nil bit-pattern as if it were a raw int and prints the
        // tag pattern itself (`3`) instead of the real value — see
        // doc/08_tracking/bug/seed_interp_flat_nullable_unwrap_wrong_value_2026-07-16.md.
        // `rt_unwrap_or_self` has the correct fallback semantics: it returns
        // the enum's payload for a genuine boxed `Enum`, and otherwise
        // returns the receiver value unchanged (already the right answer for
        // a flat-nullable's raw/tagged payload).
        // `.unwrap()` must return the Ok/Some payload for ANY enum receiver
        // (Result, Option, ...) and TRAP on Err/None — real method-call
        // semantics, distinct from `rt_unwrap_or_self` below `unwrap_or`
        // uses, which backs the never-trapping `??` operator and only
        // special-cases the reserved Option enum id (returning every other
        // enum, including Result, unchanged). Routing `.unwrap()` through
        // that operator helper silently returned the boxed `Result` enum
        // itself for `Result.Ok(v).unwrap()` instead of `v` — see
        // doc/08_tracking/bug/native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md.
        "unwrap" => "rt_unwrap_or_trap",
        // `.unwrap_or(default)` — real method-call semantics: return the
        // Ok/Some payload, or `default` on Err/None, for ANY enum receiver
        // (Result, Option, ...), never trapping. Distinct from
        // `rt_unwrap_or_self`, which the `??` operator alone must keep using
        // (see the `??` note above `.unwrap()`) — this call site now takes
        // TWO args (receiver, default), which the generic call-arg builder
        // below already threads through unmodified.
        // See doc/08_tracking/bug/native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md.
        "unwrap_or" => "rt_unwrap_or_value",
        // `.expect(msg)` — same Ok/Some-payload-or-trap semantics as
        // `.unwrap()` (see the comment above), but traps with the CALLER'S
        // message via the dedicated `rt_expect_or_trap(receiver, msg)`
        // runtime helper (mirrors the interpreter's
        // `interpreter_method/special/types.rs` `"expect"` arms) instead of
        // `.unwrap()`'s fixed "called unwrap on Err/None" text.
        //
        // This is a dedicated block (not a bare string like `unwrap` above)
        // because it takes 2 args (receiver + msg) instead of 1, so it
        // cannot reuse the shared tail below the big `match`, which always
        // declares a receiver-only signature. `.expect()` used to fail
        // entirely with "Function 'expect' not found": before this arm
        // existed, no runtime symbol of that name existed at all; the
        // interim single-receiver-arg version that followed then failed
        // closed on `ctx.runtime_funcs.get(...) else { return Ok(None) }`
        // when the symbol was not already pre-declared (which a bare
        // unannotated `.expect(msg)` call never triggers, since the
        // referenced-names pre-pass keys off `MirInst::Call`, not
        // `MirInst::MethodCallStatic`). Declare-on-demand instead of failing
        // closed.
        // See doc/08_tracking/bug/native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md.
        "expect" => {
            let msg_val = args
                .first()
                .map(|a| get_vreg_or_default(ctx, builder, a))
                .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
            let func_id = if let Some(&fid) = ctx.runtime_funcs.get("rt_expect_or_trap") {
                fid
            } else {
                let call_conv = crate::codegen::shared::platform_call_conv();
                let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                match ctx
                    .module
                    .declare_function("rt_expect_or_trap", cranelift_module::Linkage::Import, &sig)
                {
                    Ok(fid) => fid,
                    Err(_) => return Ok(None),
                }
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val, msg_val]);
            return Ok(Some(builder.inst_results(call)[0]));
        }
        "is_none" => {
            let Some(&func_id) = ctx.runtime_funcs.get("rt_is_none") else {
                return Ok(None);
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        "is_some" => {
            let Some(&func_id) = ctx.runtime_funcs.get("rt_is_some") else {
                return Ok(None);
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        "is_ok" | "is_err" => {
            let check_variant = if method == "is_ok" { "Ok" } else { "Err" };
            let disc = {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                check_variant.hash(&mut hasher);
                (hasher.finish() & 0xFFFFFFFF) as i64
            };
            let Some(&check_id) = ctx.runtime_funcs.get("rt_enum_check_discriminant") else {
                return Ok(None);
            };
            let check_ref = ctx.module.declare_func_in_func(check_id, builder.func);
            let disc_val = builder.ins().iconst(types::I64, disc);
            let call = adapted_call(builder, check_ref, &[receiver_val, disc_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        // `n.chr()` / `n.to_char()` — build a character from a code point.
        //
        // There was no arm for this anywhere on the Cranelift path, so the
        // call reached the last-resort branch in `compile_method_call_static`
        // and emitted `rt_function_not_found("i64.chr")`, which aborts with
        // "Function 'i64.chr' not found". The tree-walk interpreter
        // (interpreter_method/primitives.rs:212), the LLVM backend
        // (codegen/llvm/functions.rs:2406, functions/calls.rs:2049) and the
        // pure-Simple MIR lowering
        // (50.mir/_MirLoweringExpr/method_calls_literals.spl:1005) all
        // implement it, so ~100 `.chr()` call sites in src/lib were outages on
        // the default engine alone — including ASCII-only paths such as
        // base_encoding's `_char_from_code`.
        //
        // `method` here is the caller's `lookup_name`, which for a qualified
        // call is still the DOTTED name ("i64.chr"), hence the suffix test.
        // The receiver-type prefix is restricted to integer spellings so a
        // genuine `SomeStruct.chr` method is left to normal resolution.
        //
        // `text_dot_from_char_code` is the same runtime entry point the LLVM
        // backend calls and is non-ASCII correct (see
        // char_from_code_non_ascii_unsupported_2026-07-20). It is declared
        // explicitly because it is not an `rt_*` pre-declared import.
        //
        // doc/08_tracking/bug/text_byte_len_vs_codepoint_index_family_2026-08-06.md
        m if args.is_empty() && is_int_chr_method(m) => {
            let fid = if let Some(&existing) = ctx.func_ids.get("text_dot_from_char_code") {
                existing
            } else {
                let mut sig = Signature::new(platform_call_conv());
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                match ctx
                    .module
                    .declare_function("text_dot_from_char_code", Linkage::Import, &sig)
                {
                    Ok(id) => {
                        ctx.func_ids.insert("text_dot_from_char_code".to_string(), id);
                        id
                    }
                    Err(_) => return Ok(None),
                }
            };
            let fref = ctx.module.declare_func_in_func(fid, builder.func);
            let call = adapted_call(builder, fref, &[receiver_val]);
            return Ok(Some(builder.inst_results(call)[0]));
        }
        // Map/filter/join
        "join" => "rt_string_join",
        "merge" => {
            if args.len() == 1 {
                let other_val = get_vreg_or_default(ctx, builder, &args[0]);
                let count = inline_runtime_len_value(builder, other_val);
                if let Some(&func_id) = ctx.runtime_funcs.get("rt_array_extend_i64") {
                    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    adapted_call(builder, func_ref, &[receiver_val, other_val, count]);
                    return Ok(Some(receiver_val));
                }
            }
            return Ok(None);
        }
        "map" => {
            // Receiver-polymorphic, exactly like `at` and `index_of` below.
            //
            // This used to call `rt_option_map` directly, under a comment
            // claiming it "also works for arrays since rt_option_map checks if
            // the value is an enum with Some/None". That claim was WRONG, and
            // wrong in the direction that produces a silent answer rather than
            // an error: `rt_is_none(array)` is false, so the early return does
            // not fire; `rt_enum_payload(array)` fails its Enum type test and
            // returns NIL; the closure is then invoked EXACTLY ONCE on that
            // NIL and the result is wrapped in `Some`. `[1,2,3].map(f)`
            // answered `Some(f(nil))` — one call instead of three, on a value
            // never in the receiver — with no error and exit 0.
            //
            // `rt_map` tests the receiver: arrays get `rt_array_map`, and
            // everything else keeps the exact previous `rt_option_map` result.
            if let Some(&func_id) = ctx.runtime_funcs.get("rt_map") {
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                let closure_val = get_vreg_or_default(ctx, builder, &args[0]);
                let call = adapted_call(builder, func_ref, &[receiver_val, closure_val]);
                return Ok(Some(builder.inst_results(call)[0]));
            }
            return Ok(None);
        }
        "filter" => "rt_array_filter",
        // See calls.rs: `rt_array_sort` sorts IN PLACE and returns a bool, for
        // every receiver, and does not exist in runtime_native.c. The
        // interpreter mutates nothing and returns a new collection, which is
        // what `rt_sort` does.
        "sort" => "rt_sort",
        // See calls.rs: `rt_array_reverse` reverses IN PLACE and returns a
        // bool, for every receiver. The interpreter mutates nothing and returns
        // a new collection, which is what `rt_reverse` does.
        // MUTATING spelling — see calls.rs. `rev`/`reversed` keep `rt_reverse`.
        "reverse" => "rt_reverse_mut",
        "first" => "rt_array_first",
        "last" => "rt_array_last",
        // Receiver-polymorphic. This table had no array arm for `find` at all,
        // so `arr.find(pred)` took the string route and answered -1. `rt_find`
        // routes an array receiver with a callable closure to `rt_array_find`
        // and leaves every other shape on `rt_string_find`'s exact answer; the
        // return shape differs by receiver, which is the pre-existing contract.
        "find" => "rt_find",
        "any" => "rt_array_any",
        "all" => "rt_array_all",
        // `rt_array_enumerate` has always existed in the runtime but had no
        // dispatch arm, so `arr.enumerate()` raised "Function 'Array.enumerate'
        // not found" and still exited 0. It returns (index, item) tuples,
        // matching the interpreter.
        "enumerate" => "rt_array_enumerate",
        // String extra methods
        // `strip`/`trimmed` are interpreter-level aliases of `trim`
        // (interpreter_method/string.rs: `"trim" | "trimmed" | "strip"`).
        "trim" | "trimmed" | "strip" => "rt_string_trim",
        // `trim_left`/`trim_right`: interpreter aliases of trim_start/trim_end.
        "trim_start" | "trim_left" => "rt_string_trim_start",
        "trim_end" | "trim_right" => "rt_string_trim_end",
        "split" => "rt_string_split",
        "bytes" => "rt_string_bytes",
        "chars" => "rt_string_chars",
        "lines" | "split_lines" => "rt_string_lines",
        "replace" => "rt_string_replace",
        // See calls.rs: `.repeat()` had no runtime definition at all, so it
        // silently produced the SPECIAL_ERROR sentinel instead of a string.
        "repeat" => "rt_string_repeat",
        // See calls.rs: seven is_* spellings share four runtime entry points.
        "is_digit" | "is_numeric" => "rt_string_is_digit",
        "is_alpha" | "is_alphabetic" => "rt_string_is_alpha",
        "is_alphanumeric" | "is_alnum" => "rt_string_is_alnum",
        "is_whitespace" => "rt_string_is_whitespace",
        // See calls.rs: text methods that had no runtime definition at all.
        "char_count" => "rt_string_char_count",
        "capitalize" => "rt_string_capitalize",
        "swapcase" => "rt_string_swapcase",
        "title" | "titlecase" => "rt_string_title",
        "chomp" => "rt_string_chomp",
        "trim_start_matches" => "rt_string_trim_start_matches",
        "trim_end_matches" => "rt_string_trim_end_matches",
        "removeprefix" | "remove_prefix" => "rt_string_remove_prefix",
        "removesuffix" | "remove_suffix" => "rt_string_remove_suffix",
        "squeeze" => "rt_string_squeeze",
        "replace_first" => "rt_string_replace_first",
        "push_str" => "rt_string_concat",
        "pad_left" | "pad_start" => "rt_string_pad_left",
        "pad_right" | "pad_end" => "rt_string_pad_right",
        "center" => "rt_string_center",
        "zfill" => "rt_string_zfill",
        "find_all" | "find_indices" => "rt_string_find_all",
        // Arity-aware, see calls.rs: tagged nil and the integer 3 are the same
        // bits, so `substr`'s optional int argument needs two symbols rather
        // than a padded default. `args` here EXCLUDES the receiver.
        "substr" if args.len() >= 2 => "rt_string_substr",
        "substr" => "rt_string_substr_from",
        // See calls.rs: receiver-dispatched in the runtime, because this table
        // is keyed on the method name alone.
        "rev" | "reversed" => "rt_reverse",
        "take" | "taken" => "rt_take",
        "drop" | "dropped" | "skip" => "rt_drop",
        "sorted" => "rt_string_sorted",
        "partition" => "rt_string_partition",
        "rpartition" => "rt_string_rpartition",
        // Full alias sets, matching interpreter_method/string.rs:76-77.
        "to_upper" | "upper" | "up" | "uppercase" | "to_uppercase" => "rt_string_to_upper",
        "to_lower" | "lower" | "down" | "lowercase" | "to_lowercase" => "rt_string_to_lower",
        // `parse_i64` intentionally omitted: parse_* returns an Option in the
        // interpreter but a raw i64 here. See the note in calls.rs.
        "to_int" | "to_i64" | "parse_int" => "rt_string_to_int",
        "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => "rt_string_to_float",
        // Receiver-polymorphic: see rt_index_of.
        "index_of" => "rt_index_of",
        "find_str" => "rt_string_find",
        "rfind" | "last_index_of" => "rt_string_rfind",
        "to_string" | "to_text" | "str" => "rt_to_string",
        // Dict/collection methods
        "get" => "rt_index_get",
        // Receiver-dispatched. This table is keyed on the METHOD NAME ALONE and
        // carries no receiver type, so mapping `remove` straight to
        // `rt_dict_remove` made EVERY array `.remove(i)` a silent no-op that
        // returned nil (rt_dict_remove type-checks its receiver as a Dict and
        // takes an early-out on an Array). `rt_remove` inspects the receiver at
        // runtime, same as the `rt_pop` / `rt_reverse` / `rt_index_of` arms
        // above, and falls through to `rt_dict_remove` for non-arrays.
        // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
        "remove" => "rt_collection_remove",
        "set" => {
            if args.len() >= 2 {
                let key_val = get_vreg_or_default(ctx, builder, &args[0]);
                let val_val = get_vreg_or_default(ctx, builder, &args[1]);
                if let Some(&func_id) = ctx.runtime_funcs.get("rt_dict_set") {
                    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    let call = adapted_call(builder, func_ref, &[receiver_val, key_val, val_val]);
                    let result = builder.inst_results(call)[0];
                    return Ok(Some(super::helpers::safe_extend_to_i64(builder, result)));
                }
            }
            return Ok(None);
        }
        "keys" => "rt_dict_keys",
        "values" => "rt_dict_values",
        // `has` is the canonical Dict/Set membership idiom in Simple source;
        // rt_contains tag-dispatches on the receiver at runtime (Array/Dict/
        // String; anything else yields 0), so it is safe for untyped receivers.
        "contains_key" | "has_key" | "has" => "rt_contains",
        _ => return Ok(None),
    };

    if runtime_func == "rt_len" {
        return Ok(Some(inline_runtime_len_value(builder, receiver_val)));
    }

    // Check if runtime function exists; declare on-demand if missing
    let func_id = if let Some(&fid) = ctx.runtime_funcs.get(runtime_func) {
        fid
    } else {
        let call_conv = crate::codegen::shared::platform_call_conv();
        let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
        for _ in 0..(args.len() + 1) {
            sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
        }
        sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
        match ctx
            .module
            .declare_function(runtime_func, cranelift_module::Linkage::Import, &sig)
        {
            Ok(fid) => {
                ctx.func_ids.insert(runtime_func.to_string(), fid);
                fid
            }
            Err(_) => return Ok(None),
        }
    };

    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

    // Build call arguments: receiver first, then other args.
    // rt_array_push expects (array: RuntimeValue, value: RuntimeValue).
    // Values are already tagged RuntimeValues at this point — the MIR-level
    // BoxInt instruction handles integer tagging when needed. Do NOT
    // defensively re-box here, as that would double-tag values from function
    // calls, loads, and other sources that already return RuntimeValues.
    // Dict access routes through these tag-dispatched runtime fns, which hash the
    // key by its RtCore-tagged value. Bare collection-method args arrive UNBOXED
    // (raw native int) here, whereas the `d[k]` index path passes the key already
    // tagged — so a bare `d.get(k)`/`d.remove(k)` would hash a different key than
    // `d[k] = v` stored and silently miss (~1/4 of int keys: k ≡ 0,1 mod 8). Tag
    // the int key inline to match: rt_value_int(v) == (v << 3) | INT(0), and the
    // INT tag is 0, so a left shift by 3 suffices. Done inline, NOT via
    // wrap_value/rt_box_int, which is not linked into native AOT builds and would
    // `call 0x0`. String/heap keys are left as-is (matched by content at runtime).
    // rt_contains backs `has`/`contains_key`/`in`: for a dict it hash-looks-up
    // the key, so an int key must be tag-boxed to match how `d[k] = v` stored it
    // (otherwise `d.has(1)` misses every int key). Boxing is also correct for
    // Array.contains(int) and String.contains(int_char), whose runtime paths
    // compare against tagged RuntimeValues / call `.is_int()`.
    // `rt_collection_remove` replaced `rt_dict_remove` as the target for the
    // `remove` method name, and it MUST stay in this list. Bare collection-method
    // args arrive UNBOXED (raw native int) here, and `rt_collection_remove` takes
    // its key/index as a tagged `RuntimeValue` — dropping it from this allowlist
    // made `arr.remove(1)` and `arr.remove(2)` return nil while `arr.remove(0)`
    // worked, because the INT tag is 0 and so a raw 0 is indistinguishable from a
    // tagged 0. That "index 0 works, every other index silently fails" signature
    // is the tell for a missing tag on this path.
    // `rt_unwrap_or_value`'s second arg (`default`) is a RuntimeValue return
    // slot exactly like a dict value, and hits the same bare-arg-arrives-
    // UNBOXED-int problem as the dict-key case above: `Result.Err(e).unwrap_or
    // (9)` passed the raw untagged `9` straight through, which the runtime
    // then read back as a heap-pointer tag and printed `<invalid-heap:0x9>`
    // instead of `9`. See
    // doc/08_tracking/bug/native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md.
    let box_dict_key = matches!(
        runtime_func,
        "rt_index_get" | "rt_dict_remove" | "rt_collection_remove" | "rt_contains" | "rt_unwrap_or_value"
    );
    let key_is_int = matches!(
        ctx.vreg_types.get(args.first().unwrap_or(&receiver)).copied(),
        Some(
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
        )
    );
    let mut call_args = vec![receiver_val];
    for (arg_i, arg) in args.iter().enumerate() {
        let raw = get_vreg_or_default(ctx, builder, arg);
        let val = if box_dict_key && arg_i == 0 && key_is_int {
            builder.ins().ishl_imm(raw, 3)
        } else {
            raw
        };
        if runtime_func == "rt_array_push" && std::env::var("SIMPLE_DEBUG_PUSH").is_ok() {
            let val_ty = builder.func.dfg.value_type(val);
            let val_def = builder.func.dfg.value_def(val);
            let inst_text = match val_def {
                cranelift_codegen::ir::ValueDef::Result(inst, _) => {
                    Some(format!("{}", builder.func.dfg.display_inst(inst)))
                }
                _ => None,
            };
            eprintln!(
                "[DEBUG-PUSH] fn={} arg_vreg={:?} type_hint={:?} clif_ty={:?} value_def={:?} inst={:?}",
                ctx.func.name,
                arg,
                ctx.vreg_types.get(arg).copied(),
                val_ty,
                val_def,
                inst_text
            );
        }
        call_args.push(val);
    }

    let call = adapted_call(builder, func_ref, &call_args);
    let results = builder.inst_results(call);

    // Methods that mutate in-place (clear, reverse, sort) return the receiver.
    // push is special: rt_array_push may return a NEW pointer when the array
    // grows, so we must use the actual return value from the call.
    // NOTE: `rt_array_reverse` / `rt_array_sort` remain listed because they ARE
    // in-place if some caller names them directly. Nothing dispatches the
    // `reverse` or `sort` METHOD to them any more — both now route to the
    // copying `rt_reverse` / `rt_sort`, which must yield their RETURN value,
    // not the receiver.
    let in_place_mutating_no_push = matches!(runtime_func, "rt_array_clear" | "rt_array_reverse" | "rt_array_sort");

    if runtime_func == "rt_array_push" {
        // rt_array_push returns bool (success/failure), NOT a new array pointer.
        // The array is mutated in-place. Return the bool result.
        if results.is_empty() {
            Ok(Some(receiver_val))
        } else {
            let push_result = results[0];
            let result_type = builder.func.dfg.value_type(push_result);
            if result_type != types::I64 {
                Ok(Some(super::helpers::safe_extend_to_i64(builder, push_result)))
            } else {
                Ok(Some(push_result))
            }
        }
    } else if in_place_mutating_no_push {
        Ok(Some(receiver_val))
    } else if results.is_empty() {
        Ok(Some(builder.ins().iconst(types::I64, 0)))
    } else {
        let result = results[0];
        // Extend smaller return types (e.g., I8 from rt_contains) to I64
        let result_type = builder.func.dfg.value_type(result);
        if result_type != types::I64 {
            Ok(Some(super::helpers::safe_extend_to_i64(builder, result)))
        } else {
            Ok(Some(result))
        }
    }
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn compile_method_call_virtual<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    vtable_slot: usize,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    // Duck-typed dispatch sentinel (impl-less trait — no object carries the
    // vtable): print a named diagnostic and trap instead of jumping through
    // field data. Dead sites cost nothing; live ones fail loudly (bug
    // jit_game2d_backend_method_dispatch_sigsegv_2026-07-02).
    if vtable_slot == crate::mir::DUCK_DISPATCH_UNSUPPORTED_SLOT as usize {
        if let Ok((msg_ptr, msg_len)) = create_string_constant(
            ctx,
            builder,
            "runtime error: duck-typed virtual method call (trait has no `impl Trait for ...` in unit; no vtable) — \
             run with SIMPLE_EXECUTION_MODE=interpreter; see bug jit_game2d_backend_method_dispatch_sigsegv_2026-07-02",
        ) {
            call_runtime_2_void(ctx, builder, "rt_eprintln_str", msg_ptr, msg_len);
        }
        builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(13));
        // Unreachable continuation: satisfy the SSA builder with a fresh block.
        let cont = builder.create_block();
        builder.switch_to_block(cont);
        builder.seal_block(cont);
        if let Some(d) = dest {
            let nil = builder.ins().iconst(types::I64, 3);
            ctx.vreg_values.insert(*d, nil);
        }
        return;
    }

    let recv_ptr = get_vreg_or_default(ctx, builder, &receiver);
    // The receiver is a tagged heap value (objects are 8-byte aligned; the low
    // 3 bits hold the value tag). Mask the tag off before dereferencing to read
    // the vtable pointer stored at object[0] — the same untag compile_field_get
    // applies. Without this the load reads `object | tag` (off by the tag) and
    // the indirect call jumps to garbage. The tagged `recv_ptr` is still passed
    // as `self` below; methods untag internally on field access.
    let tag_mask = builder.ins().iconst(types::I64, !0x7i64);
    let recv_obj = builder.ins().band(recv_ptr, tag_mask);
    let vtable_ptr = builder.ins().load(types::I64, MemFlags::new(), recv_obj, 0);
    let slot_offset = (vtable_slot as i32) * 8;
    let method_ptr = builder.ins().load(types::I64, MemFlags::new(), vtable_ptr, slot_offset);

    let mut sig = Signature::new(platform_call_conv());
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![recv_ptr];
    for arg in args {
        call_args.push(get_vreg_or_default(ctx, builder, arg));
    }

    indirect_call_with_result(ctx, builder, sig_ref, method_ptr, &call_args, dest);
}

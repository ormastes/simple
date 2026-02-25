//! C code generation for individual MIR instructions.
//!
//! Dispatches each `MirInst` variant to a C code string.
//! Follows the same structure as the Cranelift `instr.rs` module.

use crate::hir::{BinOp, PointerKind, UnaryOp};
use crate::mir::{
    BlockId, ContractKind, FStringPart, MirInst, MirLiteral, MirPattern, Terminator, VReg,
};

use super::c_types::type_id_to_c_local;

/// State carried through instruction compilation for a single function.
#[derive(Default)]
pub struct CInstrContext {
    /// Accumulated C source lines for the current function body.
    pub lines: Vec<String>,
    /// String constants: (label, value)
    pub string_constants: Vec<(String, String)>,
    /// Counter for generating unique string constant labels.
    pub string_counter: usize,
}

impl CInstrContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Emit a line of C code (indented by 4 spaces).
    fn emit(&mut self, line: String) {
        self.lines.push(format!("    {}", line));
    }

    /// Register a string constant and return its label name.
    fn register_string(&mut self, value: &str) -> String {
        let label = format!("_str_{}", self.string_counter);
        self.string_counter += 1;
        self.string_constants.push((label.clone(), value.to_string()));
        label
    }

    /// Format a VReg as a C variable name.
    fn v(reg: VReg) -> String {
        format!("_v{}", reg.0)
    }

    /// Format a BlockId as a C label.
    fn bb(id: BlockId) -> String {
        format!("bb{}", id.0)
    }
}

/// Compile a single MIR instruction to C code.
pub fn compile_instruction(ctx: &mut CInstrContext, inst: &MirInst) {
    match inst {
        // =====================================================================
        // Core instructions
        // =====================================================================
        MirInst::ConstInt { dest, value } => {
            ctx.emit(format!("{} = (int64_t){};", CInstrContext::v(*dest), value));
        }

        MirInst::ConstFloat { dest, value } => {
            ctx.emit(format!("{} = {};", CInstrContext::v(*dest), format_float(*value)));
        }

        MirInst::ConstBool { dest, value } => {
            ctx.emit(format!(
                "{} = {};",
                CInstrContext::v(*dest),
                if *value { 1 } else { 0 }
            ));
        }

        MirInst::Copy { dest, src } => {
            ctx.emit(format!(
                "{} = {};",
                CInstrContext::v(*dest),
                CInstrContext::v(*src)
            ));
        }

        MirInst::BinOp {
            dest,
            op,
            left,
            right,
        } => {
            compile_binop(ctx, *dest, op, *left, *right);
        }

        MirInst::UnaryOp { dest, op, operand } => {
            compile_unaryop(ctx, *dest, op, *operand);
        }

        // =====================================================================
        // String instructions
        // =====================================================================
        MirInst::ConstString { dest, value } => {
            let label = ctx.register_string(value);
            ctx.emit(format!(
                "{} = rt_string_new((int64_t){}, (int64_t){});",
                CInstrContext::v(*dest),
                label,
                value.len()
            ));
        }

        MirInst::ConstSymbol { dest, value } => {
            // Symbols are interned strings at runtime
            let label = ctx.register_string(value);
            ctx.emit(format!(
                "{} = rt_string_new((int64_t){}, (int64_t){});",
                CInstrContext::v(*dest),
                label,
                value.len()
            ));
        }

        MirInst::FStringFormat { dest, parts } => {
            compile_fstring(ctx, *dest, parts);
        }

        // =====================================================================
        // Function call instructions
        // =====================================================================
        MirInst::Call { dest, target, args } => {
            let func_name = sanitize_name(target.name());
            let args_str = args
                .iter()
                .map(|a| CInstrContext::v(*a))
                .collect::<Vec<_>>()
                .join(", ");

            if let Some(d) = dest {
                ctx.emit(format!(
                    "{} = {}({});",
                    CInstrContext::v(*d),
                    func_name,
                    args_str
                ));
            } else {
                ctx.emit(format!("{}({});", func_name, args_str));
            }
        }

        // =====================================================================
        // Collection instructions
        // =====================================================================
        MirInst::ArrayLit { dest, elements } => {
            ctx.emit(format!(
                "{} = rt_array_new((int64_t){});",
                CInstrContext::v(*dest),
                elements.len()
            ));
            for elem in elements {
                ctx.emit(format!(
                    "rt_array_push({}, {});",
                    CInstrContext::v(*dest),
                    CInstrContext::v(*elem)
                ));
            }
        }

        MirInst::TupleLit { dest, elements } => {
            ctx.emit(format!(
                "{} = rt_tuple_new((int64_t){});",
                CInstrContext::v(*dest),
                elements.len()
            ));
            for (i, elem) in elements.iter().enumerate() {
                ctx.emit(format!(
                    "rt_tuple_set({}, (int64_t){}, {});",
                    CInstrContext::v(*dest),
                    i,
                    CInstrContext::v(*elem)
                ));
            }
        }

        MirInst::DictLit {
            dest,
            keys,
            values,
        } => {
            ctx.emit(format!(
                "{} = rt_dict_new((int64_t){});",
                CInstrContext::v(*dest),
                keys.len()
            ));
            for (k, v) in keys.iter().zip(values.iter()) {
                ctx.emit(format!(
                    "rt_dict_set({}, {}, {});",
                    CInstrContext::v(*dest),
                    CInstrContext::v(*k),
                    CInstrContext::v(*v)
                ));
            }
        }

        MirInst::IndexGet {
            dest,
            collection,
            index,
        } => {
            ctx.emit(format!(
                "{} = rt_index_get({}, {});",
                CInstrContext::v(*dest),
                CInstrContext::v(*collection),
                CInstrContext::v(*index)
            ));
        }

        MirInst::IndexSet {
            collection,
            index,
            value,
        } => {
            ctx.emit(format!(
                "rt_index_set({}, {}, {});",
                CInstrContext::v(*collection),
                CInstrContext::v(*index),
                CInstrContext::v(*value)
            ));
        }

        MirInst::SliceOp {
            dest,
            collection,
            start,
            end,
            step,
        } => {
            let s = start.map(CInstrContext::v).unwrap_or_else(|| "0".to_string());
            let e = end.map(CInstrContext::v).unwrap_or_else(|| "(int64_t)-1".to_string());
            let st = step.map(CInstrContext::v).unwrap_or_else(|| "1".to_string());
            ctx.emit(format!(
                "{} = rt_slice({}, {}, {}, {});",
                CInstrContext::v(*dest),
                CInstrContext::v(*collection),
                s,
                e,
                st
            ));
        }

        MirInst::Spread { dest, source } => {
            // Spread copies a collection (shallow clone)
            ctx.emit(format!(
                "{} = {}; /* spread (shallow copy) */",
                CInstrContext::v(*dest),
                CInstrContext::v(*source)
            ));
        }

        // =====================================================================
        // Struct/Object instructions
        // =====================================================================
        MirInst::StructInit {
            dest,
            type_id,
            struct_size,
            field_offsets,
            field_types: _,
            field_values,
        } => {
            ctx.emit(format!(
                "{} = rt_object_new((int32_t){}, (int32_t){});",
                CInstrContext::v(*dest),
                type_id.0,
                struct_size
            ));
            for (off, val) in field_offsets.iter().zip(field_values.iter()) {
                ctx.emit(format!(
                    "rt_object_field_set({}, (int32_t){}, {});",
                    CInstrContext::v(*dest),
                    off,
                    CInstrContext::v(*val)
                ));
            }
        }

        MirInst::FieldGet {
            dest,
            object,
            byte_offset,
            field_type: _,
        } => {
            ctx.emit(format!(
                "{} = rt_object_field_get({}, (int32_t){});",
                CInstrContext::v(*dest),
                CInstrContext::v(*object),
                byte_offset
            ));
        }

        MirInst::FieldSet {
            object,
            byte_offset,
            field_type: _,
            value,
        } => {
            ctx.emit(format!(
                "rt_object_field_set({}, (int32_t){}, {});",
                CInstrContext::v(*object),
                byte_offset,
                CInstrContext::v(*value)
            ));
        }

        // =====================================================================
        // Method call instructions
        // =====================================================================
        MirInst::MethodCallStatic {
            dest,
            receiver,
            func_name,
            args,
        } => {
            let name = sanitize_name(func_name);
            let mut all_args = vec![CInstrContext::v(*receiver)];
            all_args.extend(args.iter().map(|a| CInstrContext::v(*a)));
            let args_str = all_args.join(", ");

            if let Some(d) = dest {
                ctx.emit(format!("{} = {}({});", CInstrContext::v(*d), name, args_str));
            } else {
                ctx.emit(format!("{}({});", name, args_str));
            }
        }

        MirInst::MethodCallVirtual {
            dest,
            receiver,
            vtable_slot: _,
            param_types: _,
            return_type: _,
            args,
        } => {
            // Virtual dispatch: fall back to a runtime call
            let mut all_args = vec![CInstrContext::v(*receiver)];
            all_args.extend(args.iter().map(|a| CInstrContext::v(*a)));
            let args_str = all_args.join(", ");

            if let Some(d) = dest {
                ctx.emit(format!(
                    "{} = 0; /* TODO: virtual dispatch ({}) */",
                    CInstrContext::v(*d),
                    args_str
                ));
            } else {
                ctx.emit(format!("/* TODO: virtual dispatch ({}) */", args_str));
            }
        }

        MirInst::BuiltinMethod {
            dest,
            receiver,
            receiver_type,
            method,
            args,
        } => {
            compile_builtin_method(ctx, dest, *receiver, receiver_type, method, args);
        }

        // =====================================================================
        // Closure instructions
        // =====================================================================
        MirInst::ClosureCreate {
            dest,
            func_name,
            closure_size: _,
            capture_offsets,
            capture_types: _,
            captures,
        } => {
            let name = sanitize_name(func_name);
            ctx.emit(format!(
                "{} = rt_closure_new((int64_t)(intptr_t)&{}, (int32_t){});",
                CInstrContext::v(*dest),
                name,
                captures.len()
            ));
            for (i, cap) in captures.iter().enumerate() {
                let _ = capture_offsets; // offsets handled by runtime
                ctx.emit(format!(
                    "rt_closure_set_capture({}, (int32_t){}, {});",
                    CInstrContext::v(*dest),
                    i,
                    CInstrContext::v(*cap)
                ));
            }
        }

        MirInst::IndirectCall {
            dest,
            callee,
            param_types,
            return_type: _,
            args,
            effect: _,
        } => {
            // Build a C function pointer cast and call
            let params_c: Vec<&str> = param_types.iter().map(|t| type_id_to_c_local(*t)).collect();
            let params_str = if params_c.is_empty() {
                "void".to_string()
            } else {
                params_c.join(", ")
            };

            let fn_ptr = format!(
                "((int64_t(*)({}))rt_closure_func_ptr({}))",
                params_str,
                CInstrContext::v(*callee)
            );

            let args_str = args
                .iter()
                .map(|a| CInstrContext::v(*a))
                .collect::<Vec<_>>()
                .join(", ");

            if let Some(d) = dest {
                ctx.emit(format!("{} = {}({});", CInstrContext::v(*d), fn_ptr, args_str));
            } else {
                ctx.emit(format!("{}({});", fn_ptr, args_str));
            }
        }

        // =====================================================================
        // Enum instructions
        // =====================================================================
        MirInst::EnumUnit {
            dest,
            enum_name: _,
            variant_name: _,
        } => {
            // Unit enum variant = tag index as int
            // The variant index is determined at compile time; for now use a hash
            ctx.emit(format!("{} = rt_value_int(0);", CInstrContext::v(*dest)));
        }

        MirInst::EnumWith {
            dest,
            enum_name: _,
            variant_name: _,
            payload,
        } => {
            // Enum with payload: create (tag, payload) tuple
            ctx.emit(format!(
                "{} = rt_tuple_new(2);",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 0, rt_value_int(0));",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 1, {});",
                CInstrContext::v(*dest),
                CInstrContext::v(*payload)
            ));
        }

        MirInst::EnumDiscriminant { dest, value } => {
            ctx.emit(format!(
                "{} = rt_enum_discriminant({});",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        MirInst::EnumPayload { dest, value } => {
            ctx.emit(format!(
                "{} = rt_enum_payload({});",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        // =====================================================================
        // Pattern matching instructions
        // =====================================================================
        MirInst::PatternTest {
            dest,
            subject,
            pattern,
        } => {
            compile_pattern_test(ctx, *dest, *subject, pattern);
        }

        MirInst::PatternBind {
            dest,
            subject,
            binding,
        } => {
            compile_pattern_bind(ctx, *dest, *subject, binding);
        }

        // =====================================================================
        // Option/Result instructions
        // =====================================================================
        MirInst::OptionSome { dest, value } => {
            ctx.emit(format!(
                "{} = {};",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        MirInst::OptionNone { dest } => {
            ctx.emit(format!("{} = 0; /* None */", CInstrContext::v(*dest)));
        }

        MirInst::ResultOk { dest, value } => {
            // Ok: (0, value) tuple
            ctx.emit(format!(
                "{} = rt_tuple_new(2);",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 0, rt_value_int(0));",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 1, {});",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        MirInst::ResultErr { dest, value } => {
            // Err: (1, value) tuple
            ctx.emit(format!(
                "{} = rt_tuple_new(2);",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 0, rt_value_int(1));",
                CInstrContext::v(*dest)
            ));
            ctx.emit(format!(
                "rt_tuple_set({}, 1, {});",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        MirInst::TryUnwrap {
            dest,
            value,
            error_block,
            error_dest,
        } => {
            // Check if value is an error (tag == 1), branch accordingly
            ctx.emit(format!(
                "if (rt_tuple_get({}, 0) != 0) {{",
                CInstrContext::v(*value)
            ));
            ctx.emit(format!(
                "        {} = rt_tuple_get({}, 1);",
                CInstrContext::v(*error_dest),
                CInstrContext::v(*value)
            ));
            ctx.emit(format!(
                "        goto {};",
                CInstrContext::bb(*error_block)
            ));
            ctx.emit("}".to_string());
            ctx.emit(format!(
                "{} = rt_tuple_get({}, 1);",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        // =====================================================================
        // Contract instructions
        // =====================================================================
        MirInst::ContractCheck {
            condition,
            kind,
            func_name,
            message,
        } => {
            compile_contract_check(ctx, *condition, *kind, func_name, message.as_deref());
        }

        MirInst::ContractOldCapture { dest, value } => {
            ctx.emit(format!(
                "{} = {}; /* old() capture */",
                CInstrContext::v(*dest),
                CInstrContext::v(*value)
            ));
        }

        // =====================================================================
        // Pointer instructions
        // =====================================================================
        MirInst::PointerNew { dest, kind, value } => {
            let func = match kind {
                PointerKind::Unique => "rt_unique_new",
                PointerKind::Shared => "rt_shared_new",
                PointerKind::Handle => "rt_handle_new",
                _ => "rt_unique_new", // Borrow/BorrowMut/Weak default
            };
            ctx.emit(format!(
                "{} = {}({});",
                CInstrContext::v(*dest),
                func,
                CInstrContext::v(*value)
            ));
        }

        MirInst::PointerRef {
            dest,
            kind: _,
            source,
        } => {
            // Borrow reference: just copy the pointer
            ctx.emit(format!(
                "{} = {};",
                CInstrContext::v(*dest),
                CInstrContext::v(*source)
            ));
        }

        MirInst::PointerDeref {
            dest,
            pointer,
            kind,
        } => {
            let func = match kind {
                PointerKind::Unique => "rt_unique_get",
                PointerKind::Shared => "rt_shared_get",
                PointerKind::Handle => "rt_handle_get",
                _ => "rt_unique_get",
            };
            ctx.emit(format!(
                "{} = {}({});",
                CInstrContext::v(*dest),
                func,
                CInstrContext::v(*pointer)
            ));
        }

        // =====================================================================
        // Memory instructions
        // =====================================================================
        MirInst::Load { dest, addr, ty: _ } => {
            ctx.emit(format!(
                "{} = *(int64_t*)(intptr_t){};",
                CInstrContext::v(*dest),
                CInstrContext::v(*addr)
            ));
        }

        MirInst::Store {
            addr,
            value,
            ty: _,
        } => {
            ctx.emit(format!(
                "*(int64_t*)(intptr_t){} = {};",
                CInstrContext::v(*addr),
                CInstrContext::v(*value)
            ));
        }

        MirInst::LocalAddr {
            dest,
            local_index,
        } => {
            ctx.emit(format!(
                "{} = (int64_t)(intptr_t)&_local_{}; /* local addr */",
                CInstrContext::v(*dest),
                local_index
            ));
        }

        MirInst::GetElementPtr {
            dest,
            base,
            index,
        } => {
            ctx.emit(format!(
                "{} = {} + {} * 8; /* GEP */",
                CInstrContext::v(*dest),
                CInstrContext::v(*base),
                CInstrContext::v(*index)
            ));
        }

        MirInst::GcAlloc { dest, ty } => {
            ctx.emit(format!(
                "{} = rt_alloc(8); /* gc_alloc type={} */",
                CInstrContext::v(*dest),
                ty.0
            ));
        }

        MirInst::Wait { dest, target } => {
            if let Some(d) = dest {
                ctx.emit(format!(
                    "{} = rt_wait({});",
                    CInstrContext::v(*d),
                    CInstrContext::v(*target)
                ));
            } else {
                ctx.emit(format!("rt_wait({});", CInstrContext::v(*target)));
            }
        }

        // =====================================================================
        // Interpreter fallback instructions
        // =====================================================================
        MirInst::InterpCall {
            dest,
            func_name,
            args,
        } => {
            let label = ctx.register_string(func_name);
            let args_str = if args.is_empty() {
                "0, 0".to_string()
            } else {
                // Pack args into a temporary array
                let arr_name = format!("_interp_args_{}", ctx.string_counter);
                ctx.emit(format!(
                    "int64_t {}[{}];",
                    arr_name,
                    args.len()
                ));
                for (i, a) in args.iter().enumerate() {
                    ctx.emit(format!(
                        "{}[{}] = {};",
                        arr_name,
                        i,
                        CInstrContext::v(*a)
                    ));
                }
                format!(
                    "(int64_t){}, (int64_t)(intptr_t){}",
                    args.len(),
                    arr_name
                )
            };

            if let Some(d) = dest {
                ctx.emit(format!(
                    "{} = rt_interp_call((int64_t){}, (int64_t){}, {});",
                    CInstrContext::v(*d),
                    label,
                    func_name.len(),
                    args_str
                ));
            } else {
                ctx.emit(format!(
                    "rt_interp_call((int64_t){}, (int64_t){}, {});",
                    label,
                    func_name.len(),
                    args_str
                ));
            }
        }

        MirInst::InterpEval { dest, expr_index } => {
            ctx.emit(format!(
                "{} = rt_interp_eval((int64_t){});",
                CInstrContext::v(*dest),
                expr_index
            ));
        }

        // =====================================================================
        // Async/Generator/Actor stubs
        // =====================================================================
        MirInst::FutureCreate { dest, .. } => {
            ctx.emit(format!(
                "{} = 0; /* async stub: FutureCreate */",
                CInstrContext::v(*dest)
            ));
        }

        MirInst::Await { dest, future } => {
            ctx.emit(format!(
                "{} = rt_future_await({}); /* async stub */",
                CInstrContext::v(*dest),
                CInstrContext::v(*future)
            ));
        }

        MirInst::ActorSpawn { dest, .. } => {
            ctx.emit(format!(
                "{} = 0; /* async stub: ActorSpawn */",
                CInstrContext::v(*dest)
            ));
        }

        MirInst::ActorSend { actor, message } => {
            ctx.emit(format!(
                "rt_actor_send({}, {}); /* async stub */",
                CInstrContext::v(*actor),
                CInstrContext::v(*message)
            ));
        }

        MirInst::ActorRecv { dest } => {
            ctx.emit(format!(
                "{} = rt_actor_recv(); /* async stub */",
                CInstrContext::v(*dest)
            ));
        }

        MirInst::GeneratorCreate { dest, .. } => {
            ctx.emit(format!(
                "{} = 0; /* generator stub: GeneratorCreate */",
                CInstrContext::v(*dest)
            ));
        }

        MirInst::Yield { value } => {
            ctx.emit(format!(
                "(void){}; /* generator stub: Yield */",
                CInstrContext::v(*value)
            ));
        }

        MirInst::GeneratorNext { dest, generator } => {
            ctx.emit(format!(
                "{} = rt_generator_next({}); /* generator stub */",
                CInstrContext::v(*dest),
                CInstrContext::v(*generator)
            ));
        }
    }
}

/// Compile a block terminator to C code.
pub fn compile_terminator(ctx: &mut CInstrContext, term: &Terminator) {
    match term {
        Terminator::Return(Some(v)) => {
            ctx.emit(format!("return {};", CInstrContext::v(*v)));
        }

        Terminator::Return(None) => {
            ctx.emit("return 0;".to_string());
        }

        Terminator::Jump(target) => {
            ctx.emit(format!("goto {};", CInstrContext::bb(*target)));
        }

        Terminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            ctx.emit(format!(
                "if ({}) goto {}; else goto {};",
                CInstrContext::v(*cond),
                CInstrContext::bb(*then_block),
                CInstrContext::bb(*else_block)
            ));
        }

        Terminator::Unreachable => {
            ctx.emit("__builtin_trap(); /* unreachable */".to_string());
        }
    }
}

// =============================================================================
// Helper functions
// =============================================================================

/// Sanitize a function/method name for C identifier compatibility.
///
/// Replaces `::` with `__`, strips `<>`, and replaces other special chars with `_`.
pub fn sanitize_name(name: &str) -> String {
    let mut result = String::with_capacity(name.len());
    let bytes = name.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':' {
            result.push_str("__");
            i += 2;
        } else {
            match bytes[i] {
                b'<' | b'>' | b' ' | b'-' => result.push('_'),
                b'.' => result.push_str("__"),
                c => result.push(c as char),
            }
            i += 1;
        }
    }
    result
}

/// Format a float value for C, handling special cases.
fn format_float(value: f64) -> String {
    if value.is_nan() {
        "(0.0/0.0)".to_string()
    } else if value.is_infinite() {
        if value.is_sign_positive() {
            "(1.0/0.0)".to_string()
        } else {
            "(-1.0/0.0)".to_string()
        }
    } else {
        // Ensure the float has a decimal point for C
        let s = format!("{}", value);
        if s.contains('.') || s.contains('e') || s.contains('E') {
            s
        } else {
            format!("{}.0", s)
        }
    }
}

/// Compile a binary operation.
fn compile_binop(ctx: &mut CInstrContext, dest: VReg, op: &BinOp, left: VReg, right: VReg) {
    let d = CInstrContext::v(dest);
    let l = CInstrContext::v(left);
    let r = CInstrContext::v(right);

    match op {
        BinOp::Add => ctx.emit(format!("{d} = {l} + {r};")),
        BinOp::Sub => ctx.emit(format!("{d} = {l} - {r};")),
        BinOp::Mul => ctx.emit(format!("{d} = {l} * {r};")),
        BinOp::Div => ctx.emit(format!("{d} = {l} / {r};")),
        BinOp::Mod => ctx.emit(format!("{d} = {l} % {r};")),
        BinOp::Pow => ctx.emit(format!("{d} = (int64_t)pow((double){l}, (double){r});")),
        BinOp::FloorDiv => ctx.emit(format!("{d} = {l} / {r}; /* floor div */")),
        BinOp::Eq => ctx.emit(format!("{d} = (int64_t)({l} == {r});")),
        BinOp::NotEq => ctx.emit(format!("{d} = (int64_t)({l} != {r});")),
        BinOp::Lt => ctx.emit(format!("{d} = (int64_t)({l} < {r});")),
        BinOp::Gt => ctx.emit(format!("{d} = (int64_t)({l} > {r});")),
        BinOp::LtEq => ctx.emit(format!("{d} = (int64_t)({l} <= {r});")),
        BinOp::GtEq => ctx.emit(format!("{d} = (int64_t)({l} >= {r});")),
        BinOp::Is => ctx.emit(format!("{d} = (int64_t)({l} == {r}); /* is */")),
        BinOp::In => ctx.emit(format!("{d} = (int64_t)rt_contains({l}, {r});")),
        BinOp::And => ctx.emit(format!("{d} = ({l} && {r}) ? 1 : 0;")),
        BinOp::Or => ctx.emit(format!("{d} = ({l} || {r}) ? 1 : 0;")),
        BinOp::BitAnd => ctx.emit(format!("{d} = {l} & {r};")),
        BinOp::BitOr => ctx.emit(format!("{d} = {l} | {r};")),
        BinOp::BitXor => ctx.emit(format!("{d} = {l} ^ {r};")),
        BinOp::ShiftLeft => ctx.emit(format!("{d} = {l} << {r};")),
        BinOp::ShiftRight => ctx.emit(format!("{d} = {l} >> {r};")),
    }
}

/// Compile a unary operation.
fn compile_unaryop(ctx: &mut CInstrContext, dest: VReg, op: &UnaryOp, operand: VReg) {
    let d = CInstrContext::v(dest);
    let o = CInstrContext::v(operand);

    match op {
        UnaryOp::Neg => ctx.emit(format!("{d} = -{o};")),
        UnaryOp::Not => ctx.emit(format!("{d} = !{o} ? 1 : 0;")),
        UnaryOp::BitNot => ctx.emit(format!("{d} = ~{o};")),
    }
}

/// Compile f-string formatting using rt_string_concat chains.
fn compile_fstring(ctx: &mut CInstrContext, dest: VReg, parts: &[FStringPart]) {
    if parts.is_empty() {
        let label = ctx.register_string("");
        ctx.emit(format!(
            "{} = rt_string_new((int64_t){}, 0);",
            CInstrContext::v(dest),
            label
        ));
        return;
    }

    // First part
    let first = match &parts[0] {
        FStringPart::Literal(s) => {
            let label = ctx.register_string(s);
            format!("rt_string_new((int64_t){}, (int64_t){})", label, s.len())
        }
        FStringPart::Expr(reg) => {
            // Convert value to string using rt_value_to_string (or just treat as tagged)
            CInstrContext::v(*reg)
        }
    };

    if parts.len() == 1 {
        ctx.emit(format!("{} = {};", CInstrContext::v(dest), first));
        return;
    }

    // Chain remaining parts with rt_string_concat
    let mut current = format!("_fstr_tmp_{}", ctx.string_counter);
    ctx.string_counter += 1;
    ctx.emit(format!("int64_t {} = {};", current, first));

    for part in &parts[1..] {
        let next = match part {
            FStringPart::Literal(s) => {
                let label = ctx.register_string(s);
                format!("rt_string_new((int64_t){}, (int64_t){})", label, s.len())
            }
            FStringPart::Expr(reg) => CInstrContext::v(*reg),
        };
        let new_tmp = format!("_fstr_tmp_{}", ctx.string_counter);
        ctx.string_counter += 1;
        ctx.emit(format!(
            "int64_t {} = rt_string_concat({}, {});",
            new_tmp, current, next
        ));
        current = new_tmp;
    }

    ctx.emit(format!("{} = {};", CInstrContext::v(dest), current));
}

/// Compile a pattern test instruction.
fn compile_pattern_test(ctx: &mut CInstrContext, dest: VReg, subject: VReg, pattern: &MirPattern) {
    let d = CInstrContext::v(dest);
    let s = CInstrContext::v(subject);

    match pattern {
        MirPattern::Wildcard => {
            ctx.emit(format!("{d} = 1; /* wildcard always matches */"));
        }
        MirPattern::Literal(lit) => {
            let test = match lit {
                MirLiteral::Int(v) => format!("({s} == (int64_t){v})"),
                MirLiteral::Float(v) => format!("({s} == {})", format_float(*v)),
                MirLiteral::Bool(v) => format!("({s} == {})", if *v { 1 } else { 0 }),
                MirLiteral::String(val) => {
                    let label = ctx.register_string(val);
                    format!("(rt_string_eq({s}, rt_string_new((int64_t){label}, (int64_t){len})))", len = val.len())
                }
                MirLiteral::Nil => format!("({s} == 0)"),
            };
            ctx.emit(format!("{d} = (int64_t){test};"));
        }
        MirPattern::Binding(_) => {
            // Binding always matches
            ctx.emit(format!("{d} = 1; /* binding always matches */"));
        }
        MirPattern::Variant {
            enum_name: _,
            variant_name: _,
            payload: _,
        } => {
            // Check discriminant
            ctx.emit(format!("{d} = 1; /* TODO: variant pattern test */"));
        }
        MirPattern::Tuple(pats) => {
            ctx.emit(format!("{d} = (int64_t)(rt_tuple_len({s}) == (int64_t){}); /* tuple pattern */", pats.len()));
        }
        MirPattern::Struct { .. } => {
            ctx.emit(format!("{d} = 1; /* TODO: struct pattern test */"));
        }
        MirPattern::Or(pats) => {
            if pats.is_empty() {
                ctx.emit(format!("{d} = 0;"));
            } else {
                ctx.emit(format!("{d} = 0; /* or pattern */"));
                for pat in pats {
                    // Recursive test for each alternative
                    let tmp = format!("_pat_or_tmp_{}", ctx.string_counter);
                    ctx.string_counter += 1;
                    ctx.emit(format!("int64_t {tmp};"));
                    compile_pattern_test_to_var(ctx, &tmp, subject, pat);
                    ctx.emit(format!("if ({tmp}) {d} = 1;"));
                }
            }
        }
        MirPattern::Guard {
            pattern: _,
            condition,
        } => {
            ctx.emit(format!("{d} = {}; /* guard */", CInstrContext::v(*condition)));
        }
    }
}

/// Helper: compile pattern test writing to a named variable instead of VReg.
fn compile_pattern_test_to_var(
    ctx: &mut CInstrContext,
    var_name: &str,
    subject: VReg,
    pattern: &MirPattern,
) {
    let s = CInstrContext::v(subject);
    match pattern {
        MirPattern::Wildcard => ctx.emit(format!("{var_name} = 1;")),
        MirPattern::Literal(MirLiteral::Int(v)) => {
            ctx.emit(format!("{var_name} = (int64_t)({s} == (int64_t){v});"));
        }
        MirPattern::Literal(MirLiteral::Nil) => {
            ctx.emit(format!("{var_name} = (int64_t)({s} == 0);"));
        }
        _ => ctx.emit(format!("{var_name} = 1; /* TODO: complex or-subpattern */;")),
    }
}

/// Compile a pattern bind instruction.
fn compile_pattern_bind(
    ctx: &mut CInstrContext,
    dest: VReg,
    subject: VReg,
    binding: &crate::mir::PatternBinding,
) {
    let d = CInstrContext::v(dest);
    let mut current = CInstrContext::v(subject);

    for step in &binding.path {
        let tmp = format!("_bind_tmp_{}", ctx.string_counter);
        ctx.string_counter += 1;
        match step {
            crate::mir::BindingStep::TupleIndex(idx) => {
                ctx.emit(format!(
                    "int64_t {tmp} = rt_tuple_get({current}, (int64_t){idx});"
                ));
            }
            crate::mir::BindingStep::FieldName(name) => {
                let _ = name;
                ctx.emit(format!(
                    "int64_t {tmp} = {current}; /* TODO: field bind '{name}' */"
                ));
            }
            crate::mir::BindingStep::EnumPayload => {
                ctx.emit(format!(
                    "int64_t {tmp} = rt_enum_payload({current});"
                ));
            }
        }
        current = tmp;
    }

    ctx.emit(format!("{d} = {current};"));
}

/// Compile a contract check.
fn compile_contract_check(
    ctx: &mut CInstrContext,
    condition: VReg,
    kind: ContractKind,
    func_name: &str,
    message: Option<&str>,
) {
    let kind_val = match kind {
        ContractKind::Precondition => 0,
        ContractKind::Postcondition => 1,
        ContractKind::ErrorPostcondition => 2,
        ContractKind::InvariantEntry => 3,
        ContractKind::InvariantExit => 4,
    };

    let name_label = ctx.register_string(func_name);

    if let Some(msg) = message {
        let msg_label = ctx.register_string(msg);
        ctx.emit(format!(
            "simple_contract_check_msg({}, (int64_t){}, (int64_t){}, (int64_t){}, (int64_t){}, (int64_t){});",
            CInstrContext::v(condition),
            kind_val,
            name_label,
            func_name.len(),
            msg_label,
            msg.len()
        ));
    } else {
        ctx.emit(format!(
            "simple_contract_check({}, (int64_t){}, (int64_t){}, (int64_t){});",
            CInstrContext::v(condition),
            kind_val,
            name_label,
            func_name.len()
        ));
    }
}

/// Compile a builtin method call.
fn compile_builtin_method(
    ctx: &mut CInstrContext,
    dest: &Option<VReg>,
    receiver: VReg,
    receiver_type: &str,
    method: &str,
    args: &[VReg],
) {
    let recv = CInstrContext::v(receiver);
    let args_str: Vec<String> = args.iter().map(|a| CInstrContext::v(*a)).collect();

    // Map well-known builtin methods to runtime calls
    let call = match (receiver_type, method) {
        // Array methods
        (_, "push") => format!("rt_array_push({recv}, {})", args_str.first().unwrap_or(&"0".to_string())),
        (_, "pop") => format!("rt_array_pop({recv})"),
        (_, "len") | (_, "length") => format!("rt_tuple_len({recv})"), // works for arrays too
        (_, "clear") => format!("rt_array_clear({recv})"),
        (_, "get") => format!("rt_index_get({recv}, {})", args_str.first().unwrap_or(&"0".to_string())),
        (_, "set") => {
            if args_str.len() >= 2 {
                format!("rt_index_set({recv}, {}, {})", args_str[0], args_str[1])
            } else {
                format!("0 /* builtin {receiver_type}.{method} missing args */")
            }
        }
        // Dict methods
        (_, "keys") => format!("rt_dict_keys({recv})"),
        (_, "values") => format!("rt_dict_values({recv})"),
        (_, "contains") => format!("rt_contains({recv}, {})", args_str.first().unwrap_or(&"0".to_string())),
        // String concat
        (_, "concat") => format!("rt_string_concat({recv}, {})", args_str.first().unwrap_or(&"0".to_string())),
        // Default: try as Type__method
        _ => {
            let name = sanitize_name(&format!("{}::{}", receiver_type, method));
            let mut all = vec![recv.clone()];
            all.extend(args_str);
            format!("{}({})", name, all.join(", "))
        }
    };

    if let Some(d) = dest {
        ctx.emit(format!("{} = {};", CInstrContext::v(*d), call));
    } else {
        ctx.emit(format!("{};", call));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize_name() {
        assert_eq!(sanitize_name("Type::method"), "Type__method");
        assert_eq!(sanitize_name("Vec<Int>"), "Vec_Int_");
        assert_eq!(sanitize_name("my-func"), "my_func");
        assert_eq!(sanitize_name("mod.func"), "mod__func");
    }

    #[test]
    fn test_format_float() {
        assert_eq!(format_float(3.14), "3.14");
        assert_eq!(format_float(42.0), "42.0");
        assert!(format_float(f64::NAN).contains("0.0/0.0"));
        assert!(format_float(f64::INFINITY).contains("1.0/0.0"));
    }

    #[test]
    fn test_const_int_codegen() {
        let mut ctx = CInstrContext::new();
        compile_instruction(&mut ctx, &MirInst::ConstInt {
            dest: VReg(0),
            value: 42,
        });
        assert_eq!(ctx.lines.len(), 1);
        assert!(ctx.lines[0].contains("_v0 = (int64_t)42;"));
    }

    #[test]
    fn test_binop_codegen() {
        let mut ctx = CInstrContext::new();
        compile_instruction(&mut ctx, &MirInst::BinOp {
            dest: VReg(2),
            op: BinOp::Add,
            left: VReg(0),
            right: VReg(1),
        });
        assert_eq!(ctx.lines.len(), 1);
        assert!(ctx.lines[0].contains("_v2 = _v0 + _v1;"));
    }

    #[test]
    fn test_return_terminator() {
        let mut ctx = CInstrContext::new();
        compile_terminator(&mut ctx, &Terminator::Return(Some(VReg(0))));
        assert!(ctx.lines[0].contains("return _v0;"));
    }

    #[test]
    fn test_branch_terminator() {
        let mut ctx = CInstrContext::new();
        compile_terminator(&mut ctx, &Terminator::Branch {
            cond: VReg(3),
            then_block: BlockId(1),
            else_block: BlockId(2),
        });
        assert!(ctx.lines[0].contains("if (_v3) goto bb1; else goto bb2;"));
    }

    #[test]
    fn test_string_constant_registration() {
        let mut ctx = CInstrContext::new();
        compile_instruction(&mut ctx, &MirInst::ConstString {
            dest: VReg(0),
            value: "hello".to_string(),
        });
        assert_eq!(ctx.string_constants.len(), 1);
        assert_eq!(ctx.string_constants[0].0, "_str_0");
        assert_eq!(ctx.string_constants[0].1, "hello");
    }
}

// Pattern matching and enum compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{BindingStep, MirLiteral, MirPattern, PatternBinding, VReg};

use super::helpers::{call_runtime_1, call_runtime_2, call_runtime_3, create_string_constant};
use super::{InstrContext, InstrResult};

pub(crate) fn compile_pattern_test<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    pattern: &MirPattern,
) -> InstrResult<()> {
    let subject_val = ctx.vreg_values[&subject];

    // Default-off reachability probe, sharing the `subpattern_condition` switch
    // in `hir/lower/expr/control.rs` so one run instruments both seams. This
    // arm fires only for `x is Enum.Variant` / `x == Enum.Variant`; a `match`
    // never reaches here (see the module note on `compile_pattern_test`).
    if std::env::var_os("SIMPLE_DEBUG_PATTERN_LOWER").is_some() {
        eprintln!(
            "[pattern-codegen] compile_pattern_test kind={}",
            mir_pattern_kind(pattern)
        );
    }

    let result = match pattern {
        MirPattern::Wildcard => builder.ins().iconst(types::I8, 1),
        MirPattern::Literal(lit) => match lit {
            MirLiteral::Int(n) => {
                let lit_val = builder.ins().iconst(types::I64, *n);
                builder
                    .ins()
                    .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_val, lit_val)
            }
            MirLiteral::Bool(b) => {
                let lit_val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
                let subject_i8 = builder.ins().ireduce(types::I8, subject_val);
                builder
                    .ins()
                    .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_i8, lit_val)
            }
            MirLiteral::Nil => {
                // Nil is tagged value 3 (TAG_SPECIAL=0b011 | SPECIAL_NIL=0)
                let nil_val = builder.ins().iconst(types::I64, 3);
                builder
                    .ins()
                    .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_val, nil_val)
            }
            MirLiteral::String(s) => {
                // Create a runtime string from the literal and compare
                match super::helpers::create_string_constant(ctx, builder, s) {
                    Ok((str_ptr, str_len)) => {
                        // Interned literal box: this comparison re-executes per
                        // pattern test; per-eval rt_string_new leaked one
                        // registered string per execution on the no-GC tier.
                        let lit_str = call_runtime_2(ctx, builder, "rt_string_new_literal", str_ptr, str_len);
                        // Compare: rt_string_eq(subject, lit) -> i64 (0 or 1)
                        let result = call_runtime_2(ctx, builder, "rt_string_eq", subject_val, lit_str);
                        builder.ins().ireduce(types::I8, result)
                    }
                    Err(_) => {
                        // Fallback: always false
                        builder.ins().iconst(types::I8, 0)
                    }
                }
            }
            MirLiteral::Float(f) => {
                // Compare floats via bitcast to i64
                let lit_bits = f.to_bits() as i64;
                let lit_val = builder.ins().iconst(types::I64, lit_bits);
                builder
                    .ins()
                    .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_val, lit_val)
            }
        },
        MirPattern::Binding(_) => builder.ins().iconst(types::I8, 1),
        MirPattern::Variant {
            enum_name, discriminant, ..
        } => {
            // All enums now use rt_enum_new format consistently.
            // rt_enum_discriminant extracts the discriminant.
            let disc = call_runtime_1(ctx, builder, "rt_enum_discriminant", subject_val);
            let enum_id = call_runtime_1(ctx, builder, "rt_enum_id", subject_val);

            // The owning enum's declared index, fixed at MIR lowering (#6953).
            let expected_disc = i64::from(*discriminant);
            let expected_val = builder.ins().iconst(types::I64, expected_disc);
            let disc_matches = builder
                .ins()
                .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, disc, expected_val);
            let expected_id = builder.ins().iconst(
                types::I64,
                i64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
            );
            let id_matches = builder
                .ins()
                .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, enum_id, expected_id);
            builder.ins().band(disc_matches, id_matches)
        }
        // Tuple / Struct / Or / Guard / Union previously fell into a silent
        // `iconst 1` ("always match"). Nothing in the pipeline constructs those
        // today -- `MirInst::PatternTest` has exactly one non-test producer
        // (`mir/lower/lowering_expr_ops.rs`) and it only ever builds
        // `MirPattern::Variant { payload: None }` for `x is Enum.Variant`. So
        // the arm was unreachable AND, if a future front end started emitting
        // one of these, it would have mis-dispatched silently rather than
        // failing. Fail closed instead, matching the isel `case _:` precedent
        // in `doc/03_plan/compiler/native_pattern_match_staging.md` §7.
        other => {
            return Err(format!(
                "codegen: no Cranelift lowering for pattern test `{}` \
                 (only `Wildcard`, `Literal`, `Binding` and `Variant` are supported); \
                 refusing to emit an always-match test",
                mir_pattern_kind(other)
            ));
        }
    };
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Stable name for a `MirPattern` shape, for probes and error messages.
fn mir_pattern_kind(pattern: &MirPattern) -> &'static str {
    match pattern {
        MirPattern::Wildcard => "Wildcard",
        MirPattern::Literal(_) => "Literal",
        MirPattern::Binding(_) => "Binding",
        MirPattern::Variant { .. } => "Variant",
        MirPattern::Tuple(_) => "Tuple",
        MirPattern::Struct { .. } => "Struct",
        MirPattern::Or(_) => "Or",
        MirPattern::Guard { .. } => "Guard",
        MirPattern::Union { .. } => "Union",
    }
}

pub(crate) fn compile_pattern_bind<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    binding: &PatternBinding,
) {
    let mut current = ctx.vreg_values[&subject];
    for step in &binding.path {
        current = match step {
            BindingStep::EnumPayload => call_runtime_1(ctx, builder, "rt_enum_payload", current),
            BindingStep::TupleIndex(index) => {
                let index_value = builder.ins().iconst(types::I64, i64::from(*index));
                call_runtime_2(ctx, builder, "rt_tuple_get", current, index_value)
            }
            // Cranelift does not yet carry field offsets in FieldName, matching
            // the LLVM backend's current pass-through behavior.
            BindingStep::FieldName(_) => current,
        };
    }
    if ctx.vreg_types.get(&dest) == Some(&crate::hir::TypeId::U64) {
        current = call_runtime_1(ctx, builder, "rt_value_as_u64", current);
    }
    ctx.vreg_values.insert(dest, current);
}

pub(crate) fn compile_enum_unit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    enum_name: &str,
    disc: u32,
) {
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(
        types::I32,
        i64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
    );
    // Nil payload: tagged value 3 (TAG_SPECIAL=0b011 | SPECIAL_NIL=0)
    let nil_val = builder.ins().iconst(types::I64, 3);
    emit_enum_name_registration(ctx, builder, enum_name, disc, enum_id, disc_val);
    let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id, disc_val, nil_val);
    ctx.vreg_values.insert(dest, result);
}

pub(crate) fn compile_enum_with<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    enum_name: &str,
    disc: u32,
    payload: VReg,
) {
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(
        types::I32,
        i64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
    );
    let payload_val = ctx.vreg_values[&payload];
    emit_enum_name_registration(ctx, builder, enum_name, disc, enum_id, disc_val);
    let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id, disc_val, payload_val);
    ctx.vreg_values.insert(dest, result);
}

/// Emit `rt_enum_register_name(id, disc, "Enum::Variant", len, arity)` so the
/// runtime can print user enums as `Enum::Variant` instead of an address.
/// `disc` is the declared variant index into `enum_defs`; unknown rows emit
/// nothing and keep the existing fallback.
fn emit_enum_name_registration<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    enum_name: &str,
    disc: u32,
    enum_id: cranelift_codegen::ir::Value,
    disc_val: cranelift_codegen::ir::Value,
) {
    let tail = enum_name.rsplit(['.', ':']).next().unwrap_or(enum_name);
    let Some((variant, payload)) = ctx
        .enum_defs
        .get(enum_name)
        .or_else(|| ctx.enum_defs.get(tail))
        .and_then(|variants| variants.get(disc as usize))
        .cloned()
    else {
        return;
    };
    let display = format!("{tail}::{variant}");
    let arity = payload.map_or(0, |fields| fields.len() as i64);
    let Ok((ptr, len)) = create_string_constant(ctx, builder, &display) else {
        return;
    };
    let arity_val = builder.ins().iconst(types::I64, arity);
    let func_id = super::helpers::resolve_runtime_func(ctx, "rt_enum_register_name");
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let _ = super::helpers::adapted_call(builder, func_ref, &[enum_id, disc_val, ptr, len, arity_val]);
}

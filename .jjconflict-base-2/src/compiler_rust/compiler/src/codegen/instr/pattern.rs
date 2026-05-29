// Pattern matching and enum compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{BindingStep, MirLiteral, MirPattern, PatternBinding, VReg};

use super::helpers::{call_runtime_1, call_runtime_2, call_runtime_3};
use super::{InstrContext, InstrResult};

pub(crate) fn compile_pattern_test<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    pattern: &MirPattern,
) {
    let subject_val = ctx.vreg_values[&subject];

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
                        // Allocate runtime string: rt_string_new(ptr, len) -> i64
                        let lit_str = call_runtime_2(ctx, builder, "rt_string_new", str_ptr, str_len);
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
            enum_name,
            variant_name,
            ..
        } => {
            // All enums now use rt_enum_new format consistently.
            // rt_enum_discriminant extracts the discriminant.
            let disc = call_runtime_1(ctx, builder, "rt_enum_discriminant", subject_val);

            // All enums use hashed variant name discriminants consistently
            let expected_disc = calculate_variant_discriminant(variant_name) as i64;
            let expected_val = builder.ins().iconst(types::I64, expected_disc);
            builder
                .ins()
                .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, disc, expected_val)
        }
        _ => {
            // Struct/tuple patterns: always match for now (destructuring handled separately)
            builder.ins().iconst(types::I8, 1)
        }
    };
    ctx.vreg_values.insert(dest, result);
}

pub(crate) fn compile_pattern_bind<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    binding: &PatternBinding,
) {
    let current = ctx.vreg_values[&subject];

    let result = if binding.path.iter().any(|s| matches!(s, BindingStep::EnumPayload)) {
        // All enums use rt_enum_new format, so use rt_enum_payload consistently
        call_runtime_1(ctx, builder, "rt_enum_payload", current)
    } else {
        current
    };
    ctx.vreg_values.insert(dest, result);
}

/// Calculate discriminant for enum variant (stub - returns hash of name)
fn calculate_variant_discriminant(variant_name: &str) -> u32 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    variant_name.hash(&mut hasher);
    (hasher.finish() & 0xFFFFFFFF) as u32
}

pub(crate) fn compile_enum_unit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    variant_name: &str,
) {
    let disc = calculate_variant_discriminant(variant_name);
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(types::I32, 0);
    // Nil payload: tagged value 3 (TAG_SPECIAL=0b011 | SPECIAL_NIL=0)
    let nil_val = builder.ins().iconst(types::I64, 3);
    let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id, disc_val, nil_val);
    ctx.vreg_values.insert(dest, result);
}

pub(crate) fn compile_enum_with<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    variant_name: &str,
    payload: VReg,
) {
    let disc = calculate_variant_discriminant(variant_name);
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(types::I32, 0);
    let payload_val = ctx.vreg_values[&payload];
    let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id, disc_val, payload_val);
    ctx.vreg_values.insert(dest, result);
}

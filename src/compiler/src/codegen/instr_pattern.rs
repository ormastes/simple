// Pattern matching and enum compilation for codegen.
// This file is included by instr.rs.

fn compile_pattern_test<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    pattern: &MirPattern,
) {
    let subject_val = ctx.vreg_values[&subject];

    let result = match pattern {
        MirPattern::Wildcard => builder.ins().iconst(types::I8, 1),
        MirPattern::Literal(lit) => {
            match lit {
                MirLiteral::Int(n) => {
                    let lit_val = builder.ins().iconst(types::I64, *n);
                    builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_val, lit_val)
                }
                MirLiteral::Bool(b) => {
                    let lit_val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
                    let subject_i8 = builder.ins().ireduce(types::I8, subject_val);
                    builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_i8, lit_val)
                }
                MirLiteral::Nil => {
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, subject_val, zero)
                }
                _ => builder.ins().iconst(types::I8, 0),
            }
        }
        MirPattern::Binding(_) => builder.ins().iconst(types::I8, 1),
        MirPattern::Variant { .. } => {
            let disc_id = ctx.runtime_funcs["rt_enum_discriminant"];
            let disc_ref = ctx.module.declare_func_in_func(disc_id, builder.func);
            let call = builder.ins().call(disc_ref, &[subject_val]);
            let disc = builder.inst_results(call)[0];
            let neg_one = builder.ins().iconst(types::I64, -1);
            builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::NotEqual, disc, neg_one)
        }
        _ => builder.ins().iconst(types::I8, 0),
    };
    ctx.vreg_values.insert(dest, result);
}

fn compile_pattern_bind<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    subject: VReg,
    binding: &PatternBinding,
) {
    let current = ctx.vreg_values[&subject];

    let result = if binding.path.iter().any(|s| matches!(s, BindingStep::EnumPayload)) {
        let payload_id = ctx.runtime_funcs["rt_enum_payload"];
        let payload_ref = ctx.module.declare_func_in_func(payload_id, builder.func);
        let call = builder.ins().call(payload_ref, &[current]);
        builder.inst_results(call)[0]
    } else {
        current
    };
    ctx.vreg_values.insert(dest, result);
}

fn compile_enum_unit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    variant_name: &str,
) {
    let enum_new_id = ctx.runtime_funcs["rt_enum_new"];
    let enum_new_ref = ctx.module.declare_func_in_func(enum_new_id, builder.func);

    let disc = variant_name.bytes().fold(0u32, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u32));
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(types::I32, 0);
    let nil_val = builder.ins().iconst(types::I64, 0);

    let call = builder.ins().call(enum_new_ref, &[enum_id, disc_val, nil_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_enum_with<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    variant_name: &str,
    payload: VReg,
) {
    let enum_new_id = ctx.runtime_funcs["rt_enum_new"];
    let enum_new_ref = ctx.module.declare_func_in_func(enum_new_id, builder.func);

    let disc = variant_name.bytes().fold(0u32, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u32));
    let disc_val = builder.ins().iconst(types::I32, disc as i64);
    let enum_id = builder.ins().iconst(types::I32, 0);
    let payload_val = ctx.vreg_values[&payload];

    let call = builder.ins().call(enum_new_ref, &[enum_id, disc_val, payload_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

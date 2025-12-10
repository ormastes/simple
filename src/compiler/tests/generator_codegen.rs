use simple_runtime::{
    rt_generator_new, rt_generator_next, rt_value_as_int, rt_value_is_nil, RuntimeValue,
};

use simple_compiler::codegen::JitCompiler;
use simple_compiler::mir::{
    lower_generator, BlockId, LocalKind, MirBlock, MirFunction, MirInst, MirLocal, MirModule,
    Terminator, VReg,
};
use simple_compiler::hir::TypeId;
use simple_parser::Visibility;

#[test]
#[ignore = "Requires stable block layout hookup; dispatcher path covered in runtime test"]
fn jit_generator_dispatcher_yields_and_restores() {
    // Build a minimal generator body that yields 1, stores 10 across the yield, then yields 10.
    let mut func = MirFunction::new("gen_dispatcher".into(), TypeId::I64, Visibility::Public);
    func.blocks.clear();
    func.entry_block = BlockId(0);
    func.params.push(MirLocal {
        name: "generator".into(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
    });

    let mut b0 = MirBlock::new(BlockId(0));
    b0.instructions.push(MirInst::ConstInt {
        dest: VReg(0),
        value: 1,
    });
    b0.instructions.push(MirInst::Yield { value: VReg(0) });
    b0.instructions.push(MirInst::ConstInt {
        dest: VReg(1),
        value: 10,
    });
    b0.instructions.push(MirInst::Yield { value: VReg(1) });
    b0.terminator = Terminator::Return(None);
    func.blocks.push(b0);

    let lowered = lower_generator(&func, BlockId(0));
    let slot_count = lowered
        .states
        .iter()
        .map(|s| s.live_after_yield.len())
        .max()
        .unwrap_or(0) as i64;

    let mut module = MirModule::new();
    module.functions.push(lowered.rewritten);

    let mut jit = JitCompiler::new().expect("jit init");
    jit.compile_module(&module).expect("compile");
    let func_ptr = jit
        .get_function_ptr("gen_dispatcher")
        .expect("dispatcher available");

    // Create runtime generator with compiled dispatcher pointer and run it.
    let gen = rt_generator_new(func_ptr as u64, slot_count, RuntimeValue::NIL);
    let first = rt_generator_next(gen);
    assert_eq!(rt_value_as_int(first), 1);

    let second = rt_generator_next(gen);
    assert_eq!(rt_value_as_int(second), 10);

    let exhausted = rt_generator_next(gen);
    assert!(rt_value_is_nil(exhausted));
}

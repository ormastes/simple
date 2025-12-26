use simple_compiler::codegen::JitCompiler;
use simple_compiler::hir::TypeId;
use simple_compiler::mir::{
    BlockId, LocalKind, MirBlock, MirFunction, MirInst, MirLocal, MirModule, Terminator,
};
use simple_compiler::mir::CallTarget;
use simple_parser::Visibility;
use simple_runtime::aop::{AopAroundFn, ProceedContext, rt_aop_proceed};
use simple_runtime::RuntimeValue;

extern "C" fn target_sum(argc: u64, argv: *const RuntimeValue) -> RuntimeValue {
    if argc == 0 || argv.is_null() {
        return RuntimeValue::from_int(0);
    }
    let args = unsafe { std::slice::from_raw_parts(argv, argc as usize) };
    let sum = args.iter().map(|v| v.as_int()).sum::<i64>();
    RuntimeValue::from_int(sum)
}

extern "C" fn advice_add_one(
    ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let result = unsafe { rt_aop_proceed(ctx) };
    RuntimeValue::from_int(result.as_int() + 1)
}

extern "C" fn advice_mul_two(
    ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let result = unsafe { rt_aop_proceed(ctx) };
    RuntimeValue::from_int(result.as_int() * 2)
}

#[test]
fn jit_can_call_rt_aop_invoke_around() {
    let mut func = MirFunction::new("aop_invoke_wrapper".into(), TypeId::I64, Visibility::Public);
    func.blocks.clear();
    func.entry_block = BlockId(0);

    for name in ["target", "advices", "advice_len", "argc", "argv"] {
        func.params.push(MirLocal {
            name: name.into(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
        });
    }

    let mut block = MirBlock::new(BlockId(0));

    let mut loaded_params = Vec::new();
    for idx in 0..func.params.len() {
        let addr = func.new_vreg();
        block.instructions.push(MirInst::LocalAddr {
            dest: addr,
            local_index: idx,
        });
        let val = func.new_vreg();
        block.instructions.push(MirInst::Load {
            dest: val,
            addr,
            ty: TypeId::I64,
        });
        loaded_params.push(val);
    }

    let call_dest = func.new_vreg();
    block.instructions.push(MirInst::Call {
        dest: Some(call_dest),
        target: CallTarget::Pure("rt_aop_invoke_around".into()),
        args: loaded_params,
    });
    block.terminator = Terminator::Return(Some(call_dest));
    func.blocks.push(block);

    let mut module = MirModule::new();
    module.functions.push(func);

    let mut jit = JitCompiler::new().expect("jit init");
    jit.compile_module(&module).expect("compile");
    let func_ptr = jit
        .get_function_ptr("aop_invoke_wrapper")
        .expect("wrapper available");

    let advices: [AopAroundFn; 2] = [advice_add_one, advice_mul_two];
    let args = [RuntimeValue::from_int(1), RuntimeValue::from_int(2)];

    let wrapper: extern "C" fn(i64, i64, i64, i64, i64) -> i64 =
        unsafe { std::mem::transmute(func_ptr) };
    let result_raw = wrapper(
        target_sum as usize as i64,
        advices.as_ptr() as usize as i64,
        advices.len() as i64,
        args.len() as i64,
        args.as_ptr() as usize as i64,
    );

    let result = RuntimeValue::from_raw(result_raw as u64);
    assert_eq!(result.as_int(), 7);
}

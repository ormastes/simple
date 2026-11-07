/// Minimum code alignment, in bytes, for every function the seed emits.
///
/// Vendored cranelift 0.116 aligns a function to
/// `max(buffer.alignment, isa.function_alignment().minimum, symbol_alignment)`
/// and never uses `function_alignment().preferred`. On x86_64 `minimum` is 1, so
/// AOT objects got `IMAGE_SCN_ALIGN_1BYTES` text sections and functions landed
/// at odd addresses (doc/08_tracking/bug/cranelift_aot_functions_byte_aligned_2026-11-07.md).
/// The runtime reads code addresses as tagged words, and hot loops want aligned
/// entries, so every target gets at least 16 (aarch64 4, riscv64 2, s390x 4 by
/// default are all raised to 16; the per-buffer alignment can still go higher).
pub const MIN_FUNCTION_ALIGNMENT: u64 = 16;

/// Compile `ctx` and define it in `module` with at least
/// [`MIN_FUNCTION_ALIGNMENT`]. Drop-in replacement for `Module::define_function`.
pub fn define_function_aligned<M: cranelift_module::Module + ?Sized>(
    module: &mut M,
    func_id: cranelift_module::FuncId,
    ctx: &mut cranelift_codegen::Context,
) -> cranelift_module::ModuleResult<()> {
    let alignment = {
        let isa = module.isa();
        let isa_min = isa.function_alignment().minimum as u64;
        let compiled = ctx.compile(isa, &mut cranelift_codegen::control::ControlPlane::default())?;
        (compiled.buffer.alignment as u64)
            .max(isa_min)
            .max(MIN_FUNCTION_ALIGNMENT)
    };
    let compiled = ctx.compiled_code().expect("compiled code after successful compile");
    module.define_function_bytes(
        func_id,
        &ctx.func,
        alignment,
        compiled.code_buffer(),
        compiled.buffer.relocs(),
    )
}

#[path = "../../compiler/src/codegen/function_alignment.rs"]
mod function_alignment;

mod shared {
    pub use super::function_alignment::define_function_aligned;
    use cranelift_codegen::isa::CallConv;

    pub fn platform_call_conv() -> CallConv {
        if cfg!(target_os = "windows") {
            CallConv::WindowsFastcall
        } else {
            CallConv::SystemV
        }
    }
}

#[path = "../../compiler/src/codegen/cranelift_sffi.rs"]
mod cranelift_sffi;

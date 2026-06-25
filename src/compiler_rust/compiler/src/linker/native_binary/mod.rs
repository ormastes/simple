mod builder;
mod linker;
mod options;
mod platform;
mod result;
mod stubs;

pub use builder::NativeBinaryBuilder;
pub use options::NativeBinaryOptions;
pub use result::{compile_to_native_binary, NativeBinaryResult};

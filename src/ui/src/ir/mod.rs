//! Intermediate Representations for SUI templates
//!
//! - **InitIR**: State initialization instructions
//! - **TemplateIR**: Static template tree structure
//! - **RenderIR**: Dynamic rendering instructions

mod init_ir;
mod render_ir;
mod template_ir;

pub use init_ir::*;
pub use render_ir::*;
pub use template_ir::*;

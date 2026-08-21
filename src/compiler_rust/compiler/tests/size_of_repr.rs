//! Representation-size probe for the OOM investigation.
//! Prints `size_of` for the hot in-memory types. Run with `--nocapture`.

use std::mem::size_of;

#[test]
fn print_core_type_sizes() {
    macro_rules! p {
        ($t:ty) => {
            println!("{:>6}  {}", size_of::<$t>(), stringify!($t));
        };
    }
    p!(simple_compiler::value::Value);
    p!(simple_parser::ast::Expr);
    p!(simple_parser::ast::Node);
    p!(simple_parser::ast::Pattern);
    p!(simple_parser::ast::Type);
    p!(simple_parser::ast::FunctionDef);
    p!(simple_parser::ast::ClassDef);
    p!(simple_parser::ast::EnumDef);
    p!(simple_parser::ast::TraitDef);
    p!(simple_parser::ast::Module);
    p!(String);
    p!(std::sync::Arc<str>);
}

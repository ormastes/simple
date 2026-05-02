mod common;

use common::parse_and_lower;
use simple_compiler::hir::{HirType, TypeId};

#[test]
fn lowers_bitfield_definition_into_hir_type_registry() {
    let module = parse_and_lower(
        r#"
bitfield Flags(u32):
    a: 4
    b: 28

fn main() -> i64:
    return 0
"#,
    );

    let flags_id = module.types.lookup("Flags").expect("Flags type registered");
    let flags_ty = module.types.get(flags_id).expect("Flags type available");

    let HirType::Bitfield {
        name, backing, fields, ..
    } = flags_ty
    else {
        panic!("Flags should lower to HirType::Bitfield, got {flags_ty:?}");
    };

    assert_eq!(name, "Flags");
    assert_eq!(*backing, TypeId::U32);
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].name, "a");
    assert_eq!(fields[0].bit_offset, 0);
    assert_eq!(fields[0].bit_width, 4);
    assert_eq!(fields[0].ty, TypeId::U32);
    assert_eq!(fields[1].name, "b");
    assert_eq!(fields[1].bit_offset, 4);
    assert_eq!(fields[1].bit_width, 28);
    assert_eq!(fields[1].ty, TypeId::U32);
}

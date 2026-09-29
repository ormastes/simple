use super::parse_and_lower;
use crate::hir::types::TypeId;

#[test]
fn coverage_metadata_global_bool_literals_keep_native_type() {
    let module = parse_and_lower(
        "var enabled = false\nval ready = true\nconst OFF = false\nstatic active = true\nstatic mut dirty = false\nval eleven = 11\nval nineteen = 19\nfn read() -> bool:\n    enabled\n",
    ).unwrap();
    for name in ["enabled", "ready", "OFF", "active", "dirty"] {
        let (_, ty) = module.globals.iter().find(|(n, _)| n == name).expect(name);
        assert_eq!(*ty, TypeId::BOOL, "{name}");
    }
    for name in ["eleven", "nineteen"] {
        let (_, ty) = module.globals.iter().find(|(n, _)| n == name).expect(name);
        assert_eq!(*ty, TypeId::I64, "integer tag lookalike {name}");
    }
}

mod common;

use common::parse_and_lower;

#[test]
fn lowers_top_level_region_domain_blocks_to_hir_metadata() {
    let module = parse_and_lower(
        r#"
schema{Building: id Uuid}
style{Button.primary: padding 8px}

fn main() -> i64:
    return 0
"#,
    );

    assert_eq!(module.domain_blocks.len(), 2);
    assert_eq!(module.domain_blocks[0].kind, "schema");
    assert_eq!(module.domain_blocks[0].payload, "Building: id Uuid");
    assert_eq!(module.domain_blocks[0].context, "module");
    assert_eq!(module.domain_blocks[1].kind, "style");
    assert_eq!(module.domain_blocks[1].payload, "Button.primary: padding 8px");
}

#[test]
fn ignores_non_region_custom_blocks_as_domain_metadata() {
    let module = parse_and_lower(
        r#"
html{p}

fn main() -> i64:
    return 0
"#,
    );

    assert!(module.domain_blocks.is_empty());
}

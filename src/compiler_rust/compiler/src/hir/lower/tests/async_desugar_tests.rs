/// B3/B3b regression tests: generator desugar and actor desugar HIR scope visibility
///
/// Before the fix:
///   - `gen fn` generator functions with `yield` caused "yield called outside of generator"
///     in the interpreter because `val gen = ...` bound the name as "Gen" (capital G)
///     instead of "gen" due to a parser_patterns.rs inconsistency.
///   - `actor` definitions caused HIR lowering "Unknown type: ActorName" because Pass 0
///     in module_pass.rs did not register actor types as placeholders.
use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

/// B3 regression: generator function with `gen` keyword should lower without error.
/// The parser must register `val gen = ...` as the local named "gen" (lowercase),
/// not "Gen" (capitalized keyword string).
#[test]
fn test_generator_fn_lowers_without_unknown_variable() {
    let source = r#"
gen gen_counter():
    yield 1
    yield 2

fn main() -> i64:
    val result = gen_counter()
    return 0
"#;
    let result = parse_and_lower(source);
    assert!(
        result.is_ok(),
        "generator fn should lower without error, got: {:?}",
        result.err()
    );
}

/// B3 regression: `val gen = expr` must bind the name "gen" (lowercase) not "Gen".
/// Previously parser_patterns.rs mapped TokenKind::Gen -> "Gen", so `val gen = 42`
/// registered a local named "Gen" and any subsequent use of `gen` failed as unknown.
#[test]
fn test_gen_variable_name_resolves() {
    let source = r#"
fn main() -> i64:
    val gen = 42
    return gen
"#;
    let result = parse_and_lower(source);
    assert!(
        result.is_ok(),
        "`val gen = 42` should bind as local `gen` (lowercase), got: {:?}",
        result.err()
    );

    // Verify the main function is in the lowered module
    let module = result.unwrap();
    let main_fn = module.functions.iter().find(|f| f.name == "main");
    assert!(main_fn.is_some(), "main function should be in HIR");
}

/// B3b regression: `actor` definition must be registered in HIR Pass 0 as a type
/// placeholder so that `Counter { count: 0 }` in a subsequent function resolves.
#[test]
fn test_actor_type_visible_in_hir_scope() {
    let source = r#"
actor Counter:
    val count: i64

fn make_counter() -> i64:
    val c = Counter { count: 0 }
    return 0
"#;
    let result = parse_and_lower(source);
    assert!(
        result.is_ok(),
        "actor type should be registered in HIR Pass 0, got: {:?}",
        result.err()
    );

    // Verify the actor type is visible in the HIR type registry
    let module = result.unwrap();
    assert!(
        module.types.lookup("Counter").is_some(),
        "actor Counter should be registered as a HIR type"
    );
}

/// B3b regression: actor with methods should lower actor methods into HIR functions.
#[test]
fn test_actor_methods_lowered_to_hir() {
    let source = r#"
actor Counter:
    val count: i64

    fn get_count() -> i64:
        return 0
"#;
    let result = parse_and_lower(source);
    assert!(
        result.is_ok(),
        "actor with methods should lower without error, got: {:?}",
        result.err()
    );

    let module = result.unwrap();
    assert!(
        module.types.lookup("Counter").is_some(),
        "actor Counter type should be in HIR"
    );
}

/// Combined: actor type used in function body after being declared — full pipeline.
#[test]
fn test_actor_usable_after_declaration() {
    let source = r#"
actor Worker:
    val id: i64

fn spawn_worker(id: i64) -> i64:
    val w = Worker { id: id }
    return 0
"#;
    let result = parse_and_lower(source);
    assert!(
        result.is_ok(),
        "actor declared before use should lower without Unknown type error, got: {:?}",
        result.err()
    );
}

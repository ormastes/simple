// Test suite for #881: Effect Annotations (@pure, @io, @net, @fs, @unsafe, @async)
// Verifies parser correctly recognizes and stores effect decorators on functions.

use simple_parser::ast::{Effect, Node};
use simple_parser::Parser;

/// Helper to parse code and extract the first function
fn parse_and_get_function(source: &str) -> simple_parser::ast::FunctionDef {
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());

    let module = result.unwrap();
    assert!(module.items.len() >= 1, "Expected at least one item");

    if let Node::Function(func) = &module.items[0] {
        func.clone()
    } else {
        panic!("Expected function node");
    }
}

/// Test single effect annotation
fn test_single_effect(
    source: &str,
    effect: Effect,
    checker: fn(&simple_parser::ast::FunctionDef) -> bool,
) {
    let func = parse_and_get_function(source);
    assert_eq!(func.effects.len(), 1);
    assert!(func.effects.contains(&effect));
    assert!(checker(&func), "Effect checker failed");
}

/// Test multiple effects
fn test_multiple_effects_helper(
    source: &str,
    effects: Vec<Effect>,
    checkers: Vec<fn(&simple_parser::ast::FunctionDef) -> bool>,
) {
    let func = parse_and_get_function(source);
    assert_eq!(func.effects.len(), effects.len());
    for effect in &effects {
        assert!(func.effects.contains(effect));
    }
    for checker in checkers {
        assert!(checker(&func), "Effect checker failed");
    }
}

#[test]
fn test_pure_effect() {
    test_single_effect(
        r#"
@pure
fn add(x: i64, y: i64) -> i64:
    return x + y
"#,
        Effect::Pure,
        |f| f.is_pure(),
    );
}

#[test]
fn test_io_effect() {
    test_single_effect(
        r#"
@io
fn print_hello():
    print("Hello, World!")
"#,
        Effect::Io,
        |f| f.has_io(),
    );
}

#[test]
fn test_net_effect() {
    test_single_effect(
        r#"
@net
fn fetch(url: str) -> str:
    return http_get(url)
"#,
        Effect::Net,
        |f| f.has_net(),
    );
}

#[test]
fn test_fs_effect() {
    test_single_effect(
        r#"
@fs
fn read_file(path: str) -> str:
    return File.read(path)
"#,
        Effect::Fs,
        |f| f.has_fs(),
    );
}

#[test]
fn test_unsafe_effect() {
    test_single_effect(
        r#"
@unsafe
fn raw_pointer_cast(ptr: i64) -> *u8:
    return ptr as *u8
"#,
        Effect::Unsafe,
        |f| f.has_unsafe(),
    );
}

#[test]
fn test_async_effect() {
    test_single_effect(
        r#"
@async
fn delayed_task():
    await sleep(1000)
"#,
        Effect::Async,
        |f| f.is_async(),
    );
}

#[test]
fn test_multiple_effects() {
    test_multiple_effects_helper(
        r#"
@io
@net
fn fetch_and_log(url: str):
    let data = http_get(url)
    print(data)
"#,
        vec![Effect::Io, Effect::Net],
        vec![|f| f.has_io(), |f| f.has_net()],
    );
}

#[test]
fn test_three_effects() {
    test_multiple_effects_helper(
        r#"
@io
@net
@fs
fn sync_remote_file(url: str, path: str):
    let data = http_get(url)
    File.write(path, data)
    print("Synced!")
"#,
        vec![Effect::Io, Effect::Net, Effect::Fs],
        vec![|f| f.has_io(), |f| f.has_net(), |f| f.has_fs()],
    );
}

#[test]
fn test_no_effects() {
    let source = r#"
fn unrestricted_function():
    print("Can do anything!")
    http_get("https://example.com")
    File.write("/tmp/test", "data")
"#;

    let func = parse_and_get_function(source);
    assert_eq!(func.effects.len(), 0);
    assert!(!func.has_effects());
    assert!(!func.is_pure());
    assert!(!func.has_io());
    assert!(!func.has_net());
    assert!(!func.has_fs());
}

#[test]
fn test_effect_with_other_decorators() {
    let source = r#"
@pure
@inline
fn fast_add(x: i64, y: i64) -> i64:
    return x + y
"#;

    let func = parse_and_get_function(source);
    assert_eq!(func.effects.len(), 1);
    assert!(func.effects.contains(&Effect::Pure));
    assert_eq!(func.decorators.len(), 1); // @inline is not an effect
}

#[test]
fn test_effect_from_decorator_name() {
    assert_eq!(Effect::from_decorator_name("pure"), Some(Effect::Pure));
    assert_eq!(Effect::from_decorator_name("io"), Some(Effect::Io));
    assert_eq!(Effect::from_decorator_name("net"), Some(Effect::Net));
    assert_eq!(Effect::from_decorator_name("fs"), Some(Effect::Fs));
    assert_eq!(Effect::from_decorator_name("unsafe"), Some(Effect::Unsafe));
    assert_eq!(Effect::from_decorator_name("async"), Some(Effect::Async));
    assert_eq!(Effect::from_decorator_name("unknown"), None);
    assert_eq!(Effect::from_decorator_name("inline"), None);
}

#[test]
fn test_effect_decorator_name() {
    assert_eq!(Effect::Pure.decorator_name(), "pure");
    assert_eq!(Effect::Io.decorator_name(), "io");
    assert_eq!(Effect::Net.decorator_name(), "net");
    assert_eq!(Effect::Fs.decorator_name(), "fs");
    assert_eq!(Effect::Unsafe.decorator_name(), "unsafe");
    assert_eq!(Effect::Async.decorator_name(), "async");
}

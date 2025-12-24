// Test suite for #881: Effect Annotations (@pure, @io, @net, @fs, @unsafe, @async)
// Verifies parser correctly recognizes and stores effect decorators on functions.

use simple_parser::Parser;
use simple_parser::ast::{Effect, Node};

#[test]
fn test_pure_effect() {
    let source = r#"
@pure
fn add(x: i64, y: i64) -> i64:
    return x + y
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "add");
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Pure));
        assert!(func.is_pure());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_io_effect() {
    let source = r#"
@io
fn print_hello():
    print("Hello, World!")
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Io));
        assert!(func.has_io());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_net_effect() {
    let source = r#"
@net
fn fetch(url: str) -> str:
    return http_get(url)
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Net));
        assert!(func.has_net());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_fs_effect() {
    let source = r#"
@fs
fn read_file(path: str) -> str:
    return File.read(path)
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Fs));
        assert!(func.has_fs());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_unsafe_effect() {
    let source = r#"
@unsafe
fn raw_pointer_cast(ptr: i64) -> *u8:
    return ptr as *u8
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Unsafe));
        assert!(func.has_unsafe());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_async_effect() {
    let source = r#"
@async
fn delayed_task():
    await sleep(1000)
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Async));
        assert!(func.is_async());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_multiple_effects() {
    let source = r#"
@io
@net
fn fetch_and_log(url: str):
    let data = http_get(url)
    print(data)
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 2);
        assert!(func.effects.contains(&Effect::Io));
        assert!(func.effects.contains(&Effect::Net));
        assert!(func.has_io());
        assert!(func.has_net());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_three_effects() {
    let source = r#"
@io
@net
@fs
fn sync_remote_file(url: str, path: str):
    let data = http_get(url)
    File.write(path, data)
    print("Synced!")
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 3);
        assert!(func.effects.contains(&Effect::Io));
        assert!(func.effects.contains(&Effect::Net));
        assert!(func.effects.contains(&Effect::Fs));
        assert!(func.has_io());
        assert!(func.has_net());
        assert!(func.has_fs());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_no_effects() {
    let source = r#"
fn unrestricted_function():
    print("Can do anything!")
    http_get("https://example.com")
    File.write("/tmp/test", "data")
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 0);
        assert!(!func.has_effects());
        assert!(!func.is_pure());
        assert!(!func.has_io());
        assert!(!func.has_net());
        assert!(!func.has_fs());
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_effect_with_other_decorators() {
    let source = r#"
@pure
@inline
fn fast_add(x: i64, y: i64) -> i64:
    return x + y
"#;
    
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effects.len(), 1);
        assert!(func.effects.contains(&Effect::Pure));
        assert_eq!(func.decorators.len(), 1); // @inline is not an effect
    } else {
        panic!("Expected function node");
    }
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

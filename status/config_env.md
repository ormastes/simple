# Feature: ConfigEnv - Configuration Environment

**New Feature for common crate**
- **Importance**: 4/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Create a unified dictionary-like interface for accessing:
- Configuration values (from files, defaults)
- Environment variables
- Command-line arguments

## API Implemented

```rust
pub struct ConfigEnv { ... }

impl ConfigEnv {
    // Creation
    pub fn new() -> Self;
    pub fn from_args(args: &[String]) -> Self;
    pub fn from_env() -> Self;
    pub fn from_env_with_prefix(prefix: &str) -> Self;

    // Dictionary interface
    pub fn get(&self, key: &str) -> Option<&str>;
    pub fn get_or(&self, key: &str, default: &str) -> &str;
    pub fn set(&mut self, key: &str, value: &str);
    pub fn contains(&self, key: &str) -> bool;
    pub fn remove(&mut self, key: &str) -> Option<String>;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;

    // Typed getters
    pub fn get_int(&self, key: &str) -> Option<i64>;
    pub fn get_int_or(&self, key: &str, default: i64) -> i64;
    pub fn get_bool(&self, key: &str) -> Option<bool>;
    pub fn get_bool_or(&self, key: &str, default: bool) -> bool;

    // Iteration
    pub fn keys(&self) -> impl Iterator<Item = &str>;
    pub fn iter(&self) -> impl Iterator<Item = (&str, &str)>;

    // Merging (later values override earlier)
    pub fn merge(&mut self, other: &ConfigEnv);
    pub fn with_env(self) -> Self;
    pub fn with_env_prefix(self, prefix: &str) -> Self;
    pub fn with_args(self, args: &[String]) -> Self;
}
```

## TDD Approach

### Phase 1: Unit Tests - DONE
- 18 unit tests covering all functionality
- Tests for get/set, typed getters, arg parsing, merging

### Phase 2: Implementation - DONE
- HashMap-based storage
- Arg parsing (--key=value, --key value, -k value, positional)
- Env var loading (full and prefixed)
- Bool parsing (true/false/yes/no/1/0/on/off)

### Phase 3: Verify - DONE
- All 90 workspace tests pass

## Files Created/Modified

| File | Change |
|------|--------|
| `src/common/src/config_env.rs` | New module with ConfigEnv struct |
| `src/common/src/lib.rs` | Export config_env module |
| `architecture.md` | Document ConfigEnv in common |

## Progress

- [x] Status file created
- [x] Unit tests written (18 tests)
- [x] Basic get/set implemented
- [x] Env loading implemented
- [x] Arg parsing implemented
- [x] Typed getters implemented
- [x] All tests passing (90/90)

## Usage Examples

```rust
use simple_common::ConfigEnv;

// From command-line args
let config = ConfigEnv::from_args(&["--port=8080", "--verbose"]);
assert_eq!(config.get_int("port"), Some(8080));
assert_eq!(config.get_bool("verbose"), Some(true));

// From env vars with prefix
let config = ConfigEnv::from_env_with_prefix("SIMPLE_");

// Chaining sources (later overrides earlier)
let config = ConfigEnv::new()
    .with_env_prefix("SIMPLE_")
    .with_args(&args);

// Dict-like access
config.set("key", "value");
let val = config.get_or("key", "default");
```

# Rust Language Agent

**Language:** Rust
**File extensions:** `.rs`
**LSP server:** `rust-analyzer`

---

## Build & Test Commands

```bash
cargo build                         # Debug build
cargo build --release               # Release build
cargo test                          # Run all tests
cargo test test_name                # Single test
cargo clippy                        # Linter
cargo fmt                           # Formatter
cargo fmt -- --check                # Check formatting without modifying
cargo check                         # Type-check without building
```

## LSP Setup

`rust-analyzer` works out of the box with Cargo projects. Ensure `rust-analyzer` is installed:
```bash
rustup component add rust-analyzer
```

For the Simple compiler's Rust bootstrap (`src/compiler_rust/`):
```bash
cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver
```

## Style Rules

- **Ownership:** follow Rust borrow checker strictly; prefer references over cloning
- **Error handling:** use `Result<T, E>` with `?` operator; avoid `.unwrap()` in production code
- **Naming:** `snake_case` for functions/variables, `CamelCase` for types, `SCREAMING_SNAKE` for constants
- **Formatting:** always run `cargo fmt`; follow project `rustfmt.toml` if present
- **Clippy:** address all clippy warnings; use `#[allow(...)]` only with justification
- **Dependencies:** minimize external crate usage; prefer std library
- **Unsafe:** avoid `unsafe` unless absolutely necessary; document safety invariants
- **Lifetimes:** prefer elided lifetimes; name explicitly only when compiler requires it

## When To Use This Agent

Dispatch this agent when the task involves:
- Writing or editing `.rs` files
- Rust bootstrap compiler code in `src/compiler_rust/`
- Cargo configuration (`Cargo.toml`, `Cargo.lock`)
- Rust FFI bindings or `extern "C"` functions
- Performance-critical Rust code
- Rust toolchain or build configuration

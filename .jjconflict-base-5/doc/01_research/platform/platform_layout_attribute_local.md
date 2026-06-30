# Platform Layout Attribute Domain Research

Date: 2026-04-20

## External Prior Art

Rust uses `cfg` predicates with target keys such as `target_arch`, `target_os`, `target_env`, `target_abi`, `target_endian`, and `target_pointer_width`. The Rust Reference defines predicates as boolean expressions and documents pointer width values such as 16, 32, and 64 bits. It also supports `cfg_attr` to apply attributes conditionally.

Rust also has `--check-cfg`, which validates known configuration names and values. This is relevant because `@platform(cpu=linxu)` should be an error or lint, not silently ignored.

Go uses build constraints and file suffixes based on `GOOS` and `GOARCH`. The Go command documentation treats target OS, target architecture, and architecture feature tags as known terms. File names such as `source_windows_amd64.go` add implicit constraints.

Zig exposes target and layout information through compile-time facilities and builtins such as `@sizeOf`, `@alignOf`, `@offsetOf`, `@bitSizeOf`, and `@bitOffsetOf`. Zig's standard target model organizes CPU, OS, and ABI as target data rather than ad hoc strings.

## Common Design Lessons

1. Use named dimensions: CPU/arch, OS, ABI/env, endian, pointer width, and target features.
2. Validate names and values against known sets.
3. Treat target predicates as compile-time facts, not runtime checks.
4. Keep platform variability near FFI, OS, HAL, and build boundaries.
5. Prefer explicit fallback/default cases over silent fallback.
6. For layout-sensitive code, avoid order-dependent shadowing.

## Recommendation for Simple

`@platform` should be a layout/ABI attribute, not general conditional compilation. General conditional compilation can remain `@when`/`@cfg`; `@platform` should answer one question: "Which layout facts are intentional for this target?"

Recommended syntax:

```simple
@platform(bit)
@platform(default, bit=64)
@platform(cpu=x86_64, os=linux, abi=gnu, bit=64)
```

Recommended matching semantics:

- Most-specific matching wins.
- Ambiguous equal-specificity matches are errors.
- Duplicate non-default predicates are errors.
- One default fallback is allowed.

This is safer than first-match or last-match because accidental source reordering must not change ABI layout.

## Sources

- Rust Reference, Conditional compilation: https://doc.rust-lang.org/reference/conditional-compilation.html
- rustc book, Checking conditional configurations: https://doc.rust-lang.org/rustc/check-cfg.html
- Go command, Build constraints: https://pkg.go.dev/cmd/go#hdr-Build_constraints
- Zig Language Reference: https://ziglang.org/documentation/master/

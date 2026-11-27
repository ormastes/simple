# Seed parser: CppNamespace "common mistake" hint hard-fails valid `namespace` identifiers

Date: 2026-10-24
Status: FIXED 2026-10-24 (worktree simple-rel100-port-20261024, uncommitted)

## Observed

`simple compile src/app/build/targets/action_identity.spl` failed (rc=1) with
three Error-level diagnostics:

```
error: Common mistake detected: Use 'mod' instead of 'namespace'
  --> src/app/build/targets/action_identity.spl:366:9
    |
366 |     val namespace = target_cache_namespace_v1(
    |         ^
```

`namespace` is a legal Simple identifier; the file compiles on the pure-Simple
toolchain. `CommonMistake::CppNamespace` is classified Error-level in
`hint_level` and the detector in `parser/src/error_recovery.rs` fired on ANY
identifier token with lexeme `namespace`, with no context guard (unlike the
sibling `interface` dotted-path and `template` lookahead guards).

## Fix

Positive lookahead, mirroring the `JavaNew` precedent: only report when the
token FOLLOWING `namespace` is an identifier (the C++ `namespace math {}`
shape). `val namespace = ...`, `ns.namespace.len()`, and argument positions
all have non-identifier follow tokens and no longer fire.

File: `src/compiler_rust/parser/src/error_recovery.rs`
(`detect_common_mistake_lookahead`). Both emission sites
(`parser_impl/core.rs`, `parser_helpers.rs`) share this one detector.

## Verify

```
simple compile src/app/build/targets/action_identity.spl -o out.smfb
# before: 3x CppNamespace errors, rc=1
# after:  0 CppNamespace errors (compile proceeds past parse; fails later on
#         the unrelated standalone-SMF TryOperator gate, expected for this file)
```

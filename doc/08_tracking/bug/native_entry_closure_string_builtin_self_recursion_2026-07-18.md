# Native entry-closure string builtin self-recursion

**Date:** 2026-07-18
**Status:** source fixed; focused regressions pass; MCP artifact redeploy blocked by an unrelated vendored-source checksum failure.

## Symptom

An LLVM entry-closure build of `src/app/mcp/main.spl` linked successfully but
`--probe` and the stdio initialize handshake consumed CPU until timeout without
stdout or stderr. GDB stopped in `common.string_core.str_ends_with`.
Disassembly showed `str_len` and `str_ends_with` as two-byte self-loops and
`str_contains`/`str_starts_with` calling themselves.

## Root cause and fix

Entry-closure imports may represent one function with two module-local symbol
IDs. Pure-Simple UFCS resolution compared only IDs when excluding the current
function, so an imported alias could resolve `s.len()` inside `str_len` back to
the wrapper. The resolver now also rejects equal emitted symbol names.

The Rust bootstrap compiler has a separate boundary: LLVM MIR mangling could
rewrite qualified builtins such as `str.ends_with` through an imported wrapper
in `use_map`. Qualified `str.*` builtins are now preserved for the existing
runtime redirect.

## Prevention and evidence

- `resolve_nil_guard_spec.spl` constructs two IDs with the same emitted name and
  requires `try_ufcs` to reject the self-call.
- The Rust native-project test injects a conflicting `use_map` entry and
  requires `str.ends_with` to remain qualified.
- A focused native pure-Simple resolver probe passed.
- The Rust mangle regression passed.

The rebuilt pre-fix MCP artifact deterministically times out, which preserves
the end-to-end reproduction. A post-fix artifact could not be produced in this
worktree because Cargo rejects the pre-existing modified
`src/compiler_rust/vendor/zerocopy/win-cargo.bat` checksum. No vendor file was
changed or restored by this lane.

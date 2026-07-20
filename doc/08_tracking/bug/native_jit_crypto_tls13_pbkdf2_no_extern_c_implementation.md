# BUG: TLS 1.3 / PBKDF2 / Ed25519 / SIMD-row runtime symbols are registered in the master ABI list but only implemented as interpreter-only Rust builtins — no `extern "C"` or C definition for native/JIT lowering

**Status:** OPEN (not urgent — existing stub-guard fails loudly by default, see "Blast radius" below)
**Severity:** low-medium — feature gap, not silent corruption (see caveats)
**Component:** `src/compiler_rust/compiler/src/interpreter_extern/{tls13,pbkdf2}.rs`, `simd.rs` (`rt_simd_copy_row_u32`/`rt_simd_fill_row_u32`), plus 2 fully-orphaned `rt_native_profile_count`/`rt_native_profile_event`
**Found:** 2026-07-20, systematic duplicate/missing-runtime-implementation audit

## Symptom

`src/compiler_rust/common/src/runtime_symbols.rs` (`RUNTIME_SYMBOL_NAMES`,
the master ABI registry consumed by `runtime/build.rs` to build the static
symbol table used for native/JIT symbol resolution) lists 28 symbols that
have NO `#[no_mangle] extern "C"` definition and NO C definition anywhere in
the repo:

- `rt_tls13_sha256`, `rt_tls13_hkdf_extract[_into]`,
  `rt_tls13_hkdf_expand_label*` (9 variants), `rt_tls13_x25519_public_key`,
  `rt_tls13_x25519_shared_secret`, `rt_tls13_ed25519_sign` — TLS 1.3 crypto
  primitives (18 symbols)
- `rt_pbkdf2_hmac_sha1`/`sha256`/`sha384`/`sha512` — key derivation (4)
- `rt_ed25519_sign_seed`, `rt_simd_copy_row_u32`, `rt_simd_fill_row_u32` — (3)
- `rt_native_profile_count`, `rt_native_profile_event` — 0 references
  anywhere outside the registry itself; fully orphaned, likely dead entries.

All except the last 2 ARE implemented, but only as Rust `interpreter_extern`
functions (`fn rt_tls13_sha256(args: &[Value]) -> Result<Value, CompileError>`,
registered by name into the tree-walking interpreter's builtin dispatch
table via `insert_simple!("rt_tls13_sha256", tls13::rt_tls13_sha256)` in
`interpreter_extern/mod.rs`). There is no native-callable (`extern "C"`) or C
counterpart, so a native-compiled or JIT-compiled program that calls
`rt_tls13_sha256(...)` has no symbol to link against.

## Blast radius — why this is NOT the silent-corruption class

Checked `pipeline/native_project/stubs.rs::generate_stub_object` (the
auto-stub-unresolved-symbols mechanism, explicitly documented there as
existing for exactly this "self-hosted bootstrap runtime is intentionally
incomplete" class — see its comment citing memory
`simple-bootstrap-stage4-runtime-symbol-gap` and `rt_array_filter`/`rt_any_add`
as prior examples). Its `is_runtime_owned_symbol` filter EXCLUDES `rt_*`
symbols from auto-stubbing UNLESS `SIMPLE_BOOTSTRAP=1` or
`SIMPLE_STUB_MISSING_RT=1` is set. In a normal (non-bootstrap) native build,
calling one of these crypto functions from natively-compiled code produces a
genuine **linker error** ("undefined reference"), not a silently-linked
wrong-answer stub. Under `SIMPLE_BOOTSTRAP=1` it gets a weak stub (with a
`Warning: N internal Simple symbol(s) will be stubbed` printed to stderr) —
also not silent, and already a documented, deliberate bootstrap-only
trade-off, not a new discovery.

## Fix direction

Not fixed here — implementing TLS 1.3 / PBKDF2 / Ed25519 primitives in C
(or as `#[no_mangle] extern "C"` Rust) is real cryptographic work that
deserves dedicated review, not a rushed patch inside a duplicate-symbol audit
(per repo rule: fix security-relevant code deliberately, never as a
drive-by). Two safe, low-risk follow-ups if picked up later:

1. Add these 26 live-but-interpreter-only names to an explicit
   "interpreter-only, native lowering unsupported" allowlist checked at
   native/JIT codegen time, so calling them from a native-compiled program
   is a clear compile-time diagnostic instead of relying on the linker's
   (currently correct, but incidental) undefined-reference failure.
2. Delete `rt_native_profile_count`/`rt_native_profile_event` from
   `RUNTIME_SYMBOL_NAMES` (0 references anywhere else) or wire them up if
   they were meant to back a real profiling feature — currently dead
   registry entries.

## Regression coverage

Not covered by `scripts/check/check-runtime-symbol-lane-divergence.shs`
(that script targets the DUPLICATE-implementation class, not the
never-implemented-anywhere class). No regression check added for this gap in
this session — flagging via this bug doc per repo rule ("record a concrete
bug/feature request instead of silently normalizing the workaround") rather
than silently leaving it undocumented.

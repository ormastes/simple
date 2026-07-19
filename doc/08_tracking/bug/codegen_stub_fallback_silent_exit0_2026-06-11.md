# BUG: [CODEGEN-STUB-FALLBACK] silently replaces functions with empty stubs and exits 0

Status: FIXED (2026-06-11)

**Date:** 2026-06-11
**Status:** OPEN
**Severity:** High (silent miscompile)
**Found by:** memory_audit_gc_nogc nogc verification (.spipe/memory_audit_gc_nogc/research_nogc_verify.md §7 B3)

## Problem

`bin/simple compile <file> --native` on a file importing `std.gc_async_mut.gpu` prints

```
[CODEGEN-STUB-FALLBACK] ... 'gpu_global_size_z': rt_gpu_num_groups not found
```

replaces the function body with an empty stub, and **still exits 0**. The produced
binary silently does nothing where the stubbed function is called.

## Why this is bad

- A missing runtime symbol is a hard link-level error being downgraded to a warning
  string + wrong code. This is the same false-green family as compile-mode no-op
  stubs (see feedback_compile_mode_false_greens memory note).
- Combined with the gc-boundary lint not running at compile time, a nogc target can
  import gc-tree GPU code and get a silently-stubbed binary with exit 0.

## Expected

Unresolved rt_* symbols at codegen must fail the compile (non-zero exit) unless an
explicit opt-in is given.

## Fix

**File:** `src/compiler_rust/compiler/src/codegen/common_backend.rs`
**Site:** `compile_all_functions`, lines ~1434–1497 (the `failed_functions` branch)

**Change:** Inverted the gate logic.
- **Before:** default = emit stub silently; `SIMPLE_NO_STUB_FALLBACK=1` = hard error
- **After:** default = hard error listing all failing function names; `SIMPLE_ALLOW_STUB_FALLBACK` (presence, any value) = old stub path with one warning line per stubbed function to stderr

The escape hatch follows the repo convention `std::env::var_os("SIMPLE_...").is_some()`.

**Tests added** (same file, `tests` module):
- `stub_fallback_default_is_hard_error` — asserts `compile_all_functions` returns `Err` containing the function name when a body fails and `SIMPLE_ALLOW_STUB_FALLBACK` is unset
- `stub_fallback_allowed_when_env_var_set` — asserts `compile_all_functions` returns `Ok` when `SIMPLE_ALLOW_STUB_FALLBACK=1`, confirming the escape hatch works

**cargo check -p simple-compiler:** clean (0 new warnings/errors)
**cargo test -p simple-compiler stub_fallback:** 3 passed, 0 failed.

## Linker strict-mode update 2026-07-10

`SIMPLE_NO_STUB_FALLBACK=1` now emits no weak linker stubs and disables each
platform's unresolved-symbol ignore/force flags. Resolution is deferred to the
real linker after section GC, so discardable sections do not create a scanner
false positive while unresolved live calls still fail the link. Cranelift
currently emits one `.text` section per Simple module, so unused functions in
an imported module remain live together and must still be removed at the module
ownership boundary. The focused regression is
`test_no_stub_fallback_defers_unresolved_host_symbols_to_linker`.

## Focused tooling regression 2026-07-19

A non-strict incremental duplication-check build generated unresolved linker
stubs, reported success, then either scanned zero files or crashed with
`function not found: to_equal`. Repeating the build with
`SIMPLE_NO_STUB_FALLBACK=1` failed at
link time with the exact missing symbols. The unstable-build workflow now makes
strict linking mandatory for candidate and verification artifacts.

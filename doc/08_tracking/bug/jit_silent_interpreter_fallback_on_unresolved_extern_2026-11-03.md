# JIT silently falls back to the interpreter on unresolved externs (masks JIT miscompiles)

- id: jit_silent_interpreter_fallback_on_unresolved_extern_2026_11_03
- severity: P1
- status: open (guard fix-implemented-verification-pending; see below)

## Symptom
In JIT mode, stdlib crypto imports (`sha1_bytes`, sha3 paths) hit unresolved
externals (e.g. `rt_text_eq_any`, `crypto_text_to_bytes`). The whole module is
de-JITted to the interpreter, which gives correct-but-slow output and so hides
real JIT miscompiles (context: PR #6106, which closed the sha1/sha3 bugs as
fixed on the strength of interpreter-correct output).

## Finding on current release/1.0.0
The seed already has the diagnostic and strict switch; no new Rust code needed:
- `codegen/jit.rs` (`first_unresolved_import_called`) prints
  `[jit-fallback] unresolved external symbol '<name>': whole module dropped to the interpreter`
  by default, and returns a `SIMPLE_JIT_STRICT:`-tagged error under
  `SIMPLE_JIT_STRICT=1` (or `_ALL`).
- `driver/src/exec_core.rs` (~line 1010) propagates that tagged error as a
  non-zero exit instead of falling back.
Residual gaps (this bug): (1) the stderr line is easy to miss in test runners
that discard it; (2) `crypto_text_to_bytes` is a Simple-level function, not an
`rt_*` import, so it surfaces as interpreter "function not found", not via this
guard; (3) `rt_text_eq_any` has no JIT-resolvable backing.

## Repro / verification
`SIMPLE_JIT_STRICT=1 bin/simple run <script importing std sha1_bytes/sha3>`:
expect non-zero exit naming the unresolved symbol. Without it: grep stderr for
`[jit-fallback]`.

## To resolve
Back the externals (`rt_text_eq_any`, fix `crypto_text_to_bytes` import) in the
JIT path, then re-verify sha1/sha3 under `SIMPLE_JIT_STRICT=1`; run crypto
specs with strict on in CI.

## Verification 2026-11-03 (deployed seed, sha1 probe)
`use std.crypto.sha1.{sha1_bytes}; sha1_bytes("abc".bytes())` under default JIT prints
`[jit-fallback] unresolved external symbol 'crypto_text_to_bytes': whole module dropped to the interpreter ...`
plus `[engine-demotion]` lines, then correct output (len=20). Under `SIMPLE_JIT_STRICT=1` it prints
`error: ... SIMPLE_JIT_STRICT: unresolved external symbol 'crypto_text_to_bytes' ... refusing to fall back`
(non-zero exit). Diagnostic needs no new code; residual gaps (backing the externs) remain open.

## Fix 2026-11-03 (fix-implemented-verification-pending)
- `rt_text_eq_any`: added a `#[no_mangle] extern "C"` Rust twin of the C
  `runtime_native.c` function in `src/compiler_rust/runtime/src/value/collections.rs`
  (next to `rt_text_cmp_any`). The JIT symbol provider resolves `#[no_mangle]`
  runtime symbols, so the import now resolves. Cargo unit test
  `text_eq_any_tests` covers content, empty, nil and non-text words.
- Spec: `test/01_unit/app/cli/jit_text_eq_any_resolves_spec.spl` (runs under
  `SIMPLE_JIT_STRICT=1`; needs a seed rebuilt with this change).
- `crypto_text_to_bytes`: NOT a missing backing. It is an ordinary Simple fn in
  `src/lib/common/crypto/types.spl` (body calls `rt_text_to_bytes`), imported by
  `sha1.spl` etc. A JIT-compiled module that calls a Simple function defined in
  ANOTHER module sees it as an undeclared `Linkage::Import` with no provider, so
  the guard (correctly) drops the module. This is the cross-module Simple-call
  limitation of per-module JIT, not a crypto defect; fixing it needs imported
  Simple fns to be compiled/linked into the JIT module. Remains open.

## Status 2026-11-03
Status set to fix-implemented-verification-pending: `rt_text_eq_any` backing landed in f2e108e32d3 (PR #6238, merge 35c826061af); verify with `test/01_unit/app/cli/jit_text_eq_any_resolves_spec.spl` on a seed rebuilt with that change. Residual (not fixed here): `crypto_text_to_bytes` cross-module Simple-call limitation of per-module JIT; the `[jit-fallback]` diagnostic and `SIMPLE_JIT_STRICT=1` remain the guard.

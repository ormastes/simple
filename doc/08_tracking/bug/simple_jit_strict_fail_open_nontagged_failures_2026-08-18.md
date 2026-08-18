# SIMPLE_JIT_STRICT=1 was fail-open for every non-tagged JIT failure

**Status:** FIXED 2026-08-18 (this session) — `src/compiler_rust/driver/src/exec_core.rs`
**Filed:** 2026-08-18
**Found by:** rt_ alias-archaeology probes for the binary_runtime_hardening initiative
(`doc/03_plan/infra/binary_runtime_hardening/wave1_audit_results_2026-08-18.md`).

## Symptom

With `SIMPLE_JIT_STRICT=1`, `bin/simple run probe.spl` printed
`[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: codegen: 1 function body/bodies failed to compile:
[main]` and then ran the interpreter, exit 0. Strict mode is documented (and
relied on by the alias-defect bug record
`aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`) as the
way to make codegen-lane verdicts trustworthy — yet it only refused fallback
for errors carrying the literal `SIMPLE_JIT_STRICT:` tag, which is added by
`jit_strict_fallback_error_for` for a few classified families
(unresolved import, paren-less accessor, generic tagged path). Any JIT failure
that never routes through that helper — including plain Cranelift
function-body compile failures — fell back silently. Panics fell back
unconditionally.

Consequence: every codegen-lane test/benchmark verdict taken under strict mode
could actually be an interpreter result. This is precisely the "silent
interpreter fallback invalidates the result" hazard the perf-verdict rules
name.

## Fix

`exec_core.rs` catch site now checks `jit_strict_env_enabled()`
(`SIMPLE_JIT_STRICT` set and != "0") and returns a hard error for BOTH the
compile-failure arm and the panic arm, regardless of tagging. Lenient default
behavior (no env var) unchanged.

Verification: `SIMPLE_JIT_STRICT=1 bin/simple run p5.spl` (where `p5.spl` is
`fn main(): n = 5; print(n)`) must now exit non-zero with
`SIMPLE_JIT_STRICT=1: refusing interpreter fallback after JIT failure: ...`
instead of printing `5`.

## Related

The probe also exposed the underlying capability gap that triggered the
fallback: `print(<int>)` fails JIT compilation — filed separately as
`jit_cannot_compile_print_int_2026-08-18.md`.

# The Rust seed does not compile on origin/main (two independent causes)

**Filed:** 2026-08-18
**Severity:** HIGH — blocks any seed rebuild, which is the only way to verify a
fix to `jit_container_i64_boxing_truncation_2026-08-18.md`.
**Status:** cause 1 FIXED here; cause 2 OPEN.
**Found by:** `cargo check --release --bin simple` in an isolated
`CARGO_TARGET_DIR=/mnt/data/cargo-target-enginediff` (the deployed `bin/simple`
was never touched), run while root-causing the engine-differential gate.

This is the same class as
`doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`: two
independent incomplete changes, each structurally clean, together making the
tree uncompilable while the tree-structure guards stay green.
`scripts/check/check-seed-builds-push.shs` exists precisely for this and should
be red on the current tip.

---

## Cause 1 — duplicate `INLINE_INT_BITS` / `fits_inline_int` (FIXED here)

`src/compiler_rust/runtime/src/value/core.rs` carried **two copies** of the
same const and the same `const fn` inside one `impl RuntimeValue` block:

    304:    pub const INLINE_INT_BITS: u32 = 61;
    324:    pub const fn fits_inline_int(i: i64) -> bool {
    335:    pub const INLINE_INT_BITS: u32 = 61;
    354:    pub const fn fits_inline_int(i: i64) -> bool {

A botched merge. The two copies are byte-identical in body but their doc
comments contradict each other and pin down which is which:

- the FIRST says `from_int` "now consults it: values outside the range are
  heap-boxed via `from_wide_int`" and that
  `runtime/tests/boxed_int_wide_roundtrip.rs` "is the oracle and is GREEN";
- the SECOND (stale, dated 2026-08-17) says `from_int` "does NOT consult it —
  it shifts unconditionally and never heap-boxes" and that the same test file
  is "expected to be RED against this file".

The implemented `from_int` does consult `fits_inline_int`, so the first copy is
the live one. **Fix applied: deleted the second copy** (the stale 2026-08-17
block, source lines 329-358). `simple-runtime` now compiles cleanly — 13
warnings, zero errors.

## Cause 2 — still OPEN

    error[E0432]: unresolved import `crate::interpreter::module_globals_generation`
      --> compiler/src/interpreter/../interpreter_call/core/function_exec.rs:10:63
       |
    10 |     MODULE_GLOBALS_BY_OWNER, MODULE_GLOBALS_INITIAL_BY_OWNER, module_globals_generation,
       |                                                               ^^^^^^^^^^^^^^^^^^^^^^^^^ no `module_globals_generation` in `interpreter`

    error[E0599]: the method `as_ref` exists for reference `&simple_parser::FunctionDef`,
                  but its trait bounds were not satisfied
       = note: the following trait bounds were not satisfied:
               `simple_parser::FunctionDef: AsRef<_>`
               which is required by `&simple_parser::FunctionDef: AsRef<_>`

    error: could not compile `simple-compiler` (lib) due to 2 previous errors

Both are in the `simple-compiler` crate and are untouched here — they belong to
whoever landed the `module_globals_generation` and `FunctionDef` changes. Each
looks like a caller landing without its callee (or vice versa).

## Consequence

Until cause 2 is resolved, nobody can rebuild the seed, and therefore nobody
can verify a fix to the live JIT container-boxing truncation defect
(`jit_container_i64_boxing_truncation_2026-08-18.md`), whose fix sites are all
in `src/compiler_rust/`. The two are stacked: the codegen defect cannot be
closed until this builds.

# `rt_renderdoc_available()` lies `true` under the interpreter (out of N2 scope)

- **Date:** 2026-08-05
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** Medium — one honesty-contract symbol out of ten, interpreter engine only
- **Area:** `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (`renderdoc_dlopen` module)

## Summary

`rt_renderdoc_available_fn` (gpu.rs:4845-4852) reports RenderDoc as available
whenever `renderdoc_dlopen::num_captures() != u32::MAX`:

```rust
pub fn rt_renderdoc_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if renderdoc_dlopen::num_captures() != u32::MAX {
        1
    } else {
        0
    }))
}
```

But `renderdoc_dlopen::num_captures()` (gpu.rs:4831-4842) returns the plain
default `0` — not `u32::MAX` — whenever the RenderDoc API failed to resolve:

```rust
pub fn num_captures() -> u32 {
    if let Some(api) = api_ptr() {
        unsafe { /* ... call the real GetNumCaptures ... */ }
    }
    0
}
```

So on any host without a resident RenderDoc (i.e. the normal case, including
this dev host), `num_captures()` is `0`, `0 != u32::MAX` is `true`, and
`rt_renderdoc_available()` reports **1 (available)** even though
`RENDERDOC_GetAPI` was never resolved. Confirmed empirically:

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple test test/01_unit/runtime/renderdoc_honesty_spec.spl --no-cache --no-cover-check
✗ rt_renderdoc_available reports 0 -- RENDERDOC_GetAPI never resolved here
    expected 1 to equal 0
```

## Scope note

Discovered while implementing Task #62 Lane N2
(`doc/03_plan/runtime/native_binding/dlopen_conversion_lanes.md`), which adds
the honest, dlopen-based `rt_renderdoc_*` C shim
(`src/runtime/runtime_renderdoc.c`) for the native/compiled-code path. That
shim's `rt_renderdoc_available()` is correctly honest (verified via
`native-build`, sabotage-tested). This bug is in a **separate** code path
(the Rust interpreter's own dlopen-based `renderdoc_dlopen` module in
`gpu.rs`, used only when the tree-walk interpreter executes the extern call)
that Lane N2's owns-list does not include, so it is filed here rather than
fixed inline.

## Suggested fix

Expose a small `pub fn available() -> bool { api_ptr().is_some() }` in the
`renderdoc_dlopen` module and have `rt_renderdoc_available_fn` use it instead
of the `num_captures() != u32::MAX` sentinel comparison. Requires a Rust seed
rebuild (`cargo build`) to take effect in `bin/simple test`'s interpreter
engine — not done here per `.claude/rules/bootstrap.md` ("no bootstrap unless
essential"; budget rebuilds deliberately rather than as a side effect of an
unrelated lane).

## Evidence

- `test/01_unit/runtime/renderdoc_honesty_spec.spl` — the "available reports
  0" example is RED against the deployed seed today; all seven other
  `rt_renderdoc_*` honesty examples pass under the interpreter (they don't
  route through the buggy comparison).

## Resolution (2026-08-05, task #93)

Fixed exactly per the suggested shape above: added
`pub fn available() -> bool { api_ptr().is_some() }` to the `renderdoc_dlopen`
module (`gpu.rs`) and switched `rt_renderdoc_available_fn` to call it instead
of the `num_captures() != u32::MAX` sentinel comparison. This landed earlier
the same session as commit `87bda4ffc7d208b36495822b16d2a915a2bee0f8`
("fix(rt-gpu): report renderdoc availability from actual dlopen resolution"),
already on `origin/main` by the time this task started — this task's job was
to independently re-verify it (source diff alone is not proof; the memory
note `reference_bin_simple_symlink_stale_scratch_build_and_verify_binary_provenance.md`
and `reference_test_daemon_freezes_env_selectors_stale_not_empty.md` both warn
that a source fix without a matching binary rebuild is not evidence of
anything) and close out this doc.

**Rebuild:** an ad-hoc incremental `cargo build --bin simple` (debug profile,
in `src/compiler_rust/`) was sufficient — no full bootstrap needed, per
`.claude/rules/bootstrap.md`. One wrinkle: a stale `light_daemon.spl` test
daemon (PID holding `target/debug/simple` built *before* the fix commit) was
still resident from an earlier session and was serving cached results; it was
killed (`kill -9`) before the rebuilt binary's fix was observed. `cargo build
-p simple-compiler --lib` also verified a clean compile of the crate housing
the module.

**Verdict (post-fix, post-rebuild, daemon killed):**

```
SIMPLE_EXECUTION_MODE=interpret bin/simple test test/01_unit/runtime/renderdoc_honesty_spec.spl --no-cache --no-cover-check
SPEC FILE VERDICT: test/01_unit/runtime/renderdoc_honesty_spec.spl declared>=8 executed=8 passed=8 failed=0 dropped=0
PASS test/01_unit/runtime/renderdoc_honesty_spec.spl
```

All 8 `rt_renderdoc_*` honesty examples pass, including the previously-red
"available reports 0" one; the 7 that already passed did not regress.

**Sabotage receipt:** reverted `rt_renderdoc_available_fn` to
`renderdoc_dlopen::num_captures() != u32::MAX`, rebuilt, reran the spec — the
exact original failure text reappeared verbatim:

```
✗ rt_renderdoc_available reports 0 -- RENDERDOC_GetAPI never resolved here
    expected 1 to equal 0
SPEC FILE VERDICT: ... executed=8 passed=7 failed=1 dropped=0
```

Reverted the sabotage back to `renderdoc_dlopen::available()` (file diff
against HEAD confirmed clean afterward — byte-identical to the committed
fix), rebuilt again, and reconfirmed green (`passed=8 failed=0 dropped=0`).

**Rust-level check:** `cargo build -p simple-compiler --lib` compiles clean.
`renderdoc_dlopen` has no dedicated `#[test]` unit tests of its own (the
nearby `#[cfg(test)] mod cuda_status_tests` in the same file is unrelated,
CUDA-status only); ran `cargo test -p simple-compiler --lib gpu::` as the
closest existing coverage for the file — 80 passed, 0 failed, no regression.

No code changes were pushed by this task (the fix commit was already on
`origin/main`); only this doc's status/Resolution update was committed.

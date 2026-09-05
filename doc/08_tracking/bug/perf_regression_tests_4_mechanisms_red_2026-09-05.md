# check-perf-regression-tests.shs: 4 mechanisms RED (2026-09-05)

## Status

Push-tier ADVISORY gate (`config/check/must_check_gates.sdn`,
`push-perf-regression-tests`). Advisory means it runs and RECORDS its verdict
on stderr without blocking the push — an advisory verdict is never a pass.
Not touched by this record; **do not fix and do not weaken the gate.**

## Exact gate output (verified 2026-09-05, host darwin/arm64)

```
$ sh scripts/check/check-perf-regression-tests.shs
...
FAIL — 191 mechanism(s) checked, 4 regressed: pure-interp array push through
owner HOPPARK test pins clone budget at every depth ANYVTJIT seed: aggregate
copy keeps vtable hdr IMPORTASTMEMO seed: memo cleared with the loader caches
```
Exit code 1.

## The 4 mechanisms

Each is a `must_contain <label> <file> <exact-needle>` check in
`scripts/check/check-perf-regression-tests.shs`. A mechanism goes red when the
pinned file no longer contains the exact needle text — i.e. the fix it
guards was refactored (function renamed/moved/re-exported) without updating
the guard's pinned string, not necessarily that the underlying perf fix was
reverted.

### 1. "pure-interp array push through owner"

- **Pins:** `scripts/check/check-perf-regression-tests.shs:274` — expects
  `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl`
  to contain `val_arrays[receiver].push(new_elem)`, guarding
  `doc/08_tracking/bug/pure_interp_cow_alias_primitives_2026-08-22.md` (array
  `.push` must write through the owner, not a temp alias that COW-deep-copies
  the whole array per write — measured 22.3s vs 1ms at N=16k under the old
  alias pattern).
- **What changed:** the call site was refactored to
  `val _ = val_array_push(receiver, new_elem)` (verified at
  `call_method_eval.spl:954`) — the push now goes through a named helper
  function instead of the inline `val_arrays[receiver].push(...)` expression
  the guard was written against.
- **Unblock condition:** confirm `val_array_push(receiver, new_elem)` still
  mutates `val_arrays[receiver]` in place (through the owner, no
  read-modify-write-back alias) rather than reintroducing the O(N) COW copy,
  then update the guard's needle to match the helper-based call site (or to
  grep inside `val_array_push`'s own body for the owner-write). Do not widen
  the check to `must_contain ... "push"` — that would stop discriminating the
  original defect.

### 2. "HOPPARK test pins clone budget at every depth"

- **Pins:** `scripts/check/check-perf-regression-tests.shs:515` — expects
  `src/compiler_rust/compiler/tests/interpreter_receiver_hop_depth_linear.rs`
  to contain `for depth in 1..=3usize {`, guarding the receiver-hop clone
  budget staying linear (not quadratic) across every depth 1..3.
- **What changed:** the test now iterates
  `for depth in [0usize, 1, 3] {` (verified at line 118) — depth 0 was added
  and depth 2 was dropped from the sweep.
- **Unblock condition:** confirm the test still exercises a monotonic
  depth range wide enough to catch quadratic blowup (a sweep that skips depth
  2 is weaker evidence than the original 1,2,3 run), then update the guard's
  needle to the new loop header. If the omission of depth 2 is deliberate,
  say so in the test's own comment before repinning the guard against it.

### 3. "ANYVTJIT seed: aggregate copy keeps vtable hdr"

- **Pins:** `scripts/check/check-perf-regression-tests.shs:542` — expects
  `src/compiler_rust/compiler/src/codegen/instr/mod.rs` to contain the exact
  substring `*byte_size + 8, &shifted`, guarding that a by-value copy of a
  vtable-bearing struct includes the 8-byte vtable header (part of the
  ANYVTJIT erased-receiver dispatch fix, 2026-08-22).
- **What changed:** the code was refactored from an inline expression to a
  named local: `shifted_offsets = field_offsets.iter().map(|o| o + 8).collect()`
  (verified at lines 970-973) — the `+ 8` header-shift logic is present but no
  longer spelled `*byte_size + 8, &shifted` anywhere in the file.
- **Unblock condition:** confirm `shifted_offsets` is used everywhere the old
  inline `&shifted` slice was used (i.e. the header-inclusive copy is still
  wired into the actual copy-emission call, not just computed and discarded),
  then update the guard's needle to `.map(|o| o + 8).collect()` or an
  equivalent stable anchor in the new code shape.

### 4. "IMPORTASTMEMO seed: memo cleared with the loader caches"

- **Pins:** `scripts/check/check-perf-regression-tests.shs:589` — expects
  `src/compiler_rust/compiler/src/module_cache.rs` to contain the exact call
  `crate::hir::lower::import_loader::clear_imported_module_ast_cache();`,
  guarding that the parsed-module-AST memo (which took a trivial lint from
  3,819 to 676 `.spl` opens) is cleared alongside the other loader caches so
  a stale AST can't survive a cache-clearing event.
- **What changed:** the function was re-exported one level up — the module
  now calls `crate::hir::lower::clear_imported_module_ast_cache();` (verified
  twice, at `module_cache.rs:174` and `:242`), dropping the `::import_loader::`
  path segment from the call site.
- **Unblock condition:** confirm `crate::hir::lower::clear_imported_module_ast_cache`
  is genuinely the same function re-exported (not a different, no-op stub)
  from `hir::lower`'s own module root, then update the guard's needle to the
  shorter path — and confirm it still fires at both clear sites, not just one,
  since the guard as currently written would silently pass on either one
  alone.

## What this record does NOT do

- Does not edit `scripts/check/check-perf-regression-tests.shs`.
- Does not weaken, skip, or `--expect`-escape the gate.
- Does not assert the 4 underlying perf fixes have regressed in behavior —
  only that their guards' pinned text no longer matches, which is a distinct
  (and prior, and necessary-to-resolve-first) question from whether the fixes
  still hold. Resolving each item requires actually re-verifying the
  behavior described in its linked `doc/08_tracking/bug/` record, not just
  restoring string-match.

# 12 verification/assurance specs are stably broken, not flaky — and one is a parser defect

Status: OPEN
Found: 2026-08-21
Area: `test/01_unit/compiler/verification/`, `test/01_unit/compiler/assurance/`,
`src/compiler/00.common/assurance/`

## Summary

18 specs from the `async` / `verification` / `assurance` block that looked
unstable were each run **3× with `timeout 300`**. **Every one was STABLE** —
same verdict, same `executed`/`passed`/`failed` counts on all three runs.
**Zero were flaky.**

- **6** were artifacts of single-worker **test-daemon head-of-line blocking**
  (`daemon-backlog: N request(s) queued…`), fixed by `7a6f6459a81`. They are
  stably `OK` now; per-spec cost fell ~51 s → ~7.5 s.
- **12** are stably `ERROR` — hard, reproducible failures.

These 12 sit on the "Flaky Tests" list in
`doc/08_tracking/test/test_result.md`, whose stated criterion is *"high
variance in execution time"*. Being labelled flaky is why they have been
ignored. Per repo rules a failing test is not to be skipped or dismissed
without approval; this record exists so none of the 12 is silently carried.

## The 12, with root cause

### Never execute at all (highest priority — zero signal today)

1. **`assurance/formal_delivery_gates_spec.spl`** — `executed=0`.
   `error: compile failed: parse: in
   "src/compiler/00.common/assurance/formal_delivery_gates.spl": Unexpected
   token: expected expression, found Dedent`.

   The construct at `formal_delivery_gates.spl:127-131` (and again at
   `185-189`) is a multi-line `if` condition continued on trailing `or`:

   ```
   if not delivery_hashes_closed_v1(item.receipt_hashes) or
           not sha256_lower_hex_valid(item.evidence_hash) or
           item.diagnostic != "":
       return FormalDeliveryDecisionV1(false, false, highest, "", ...)
   ```

   This is a short, safe, compact form and the parser rejects it. Per
   `CLAUDE.md` ("When a short, safe grammar or compact expression form fails
   … fix it or record a concrete bug/feature request instead of silently
   normalizing the workaround") this is recorded rather than worked around:
   wrapping the condition in parentheses would hide a real grammar gap.
   **The fix belongs in the parser (`src/compiler/10.frontend/**`), which is
   owned by another agent — not edited here.**

2. **`verification/lean_workflow_spec.spl`** — `executed=0`.
   `error: runtime: Module "io" does not export 'fs'`. Broken import.

### Compiler / type defects (4)

3. **`assurance/sha512_integrity_receipt_spec.spl`** — 3 exec / 2 fail.
   `semantic: invalid assignment: cannot index assign value of type array`,
   reached through `sha512_text`; the index-assign is
   `src/lib/common/crypto/sha512.spl:226` (`padded[pi] = padded[pi] & 255`).
   The one passing example is the early-return rejection path that never
   computes a digest.
4. **`verification/lean_block_integration_spec.spl`** — 10/1.
   `semantic: class 'LeanBlock' has no field named 'namespace'`.
5. **`verification/unsupported_construct_spec.spl`** — 15 exec / **14 fail**.
   `semantic: function expects 1 argument(s), but 2 were provided`. Worst of
   the set.
6. **`verification/verification_diagnostics_spec.spl`** — 5/2.
   `semantic: method 'format' not found on type 'dict'`.

### Assertion drift — spec and subject disagree (6)

7. `verification/proof_reference_spec.spl` — 11/2. Compares an
   `Option::Some(...)` against `to_contain` without unwrapping.
8. `verification/lean_basic_spec.spl` — 5/1. `expected true to equal false`
   on the sorry-disabled fail-closed path.
9. `verification/lean_codegen_spec.spl` — 5/1. `expected subject to be
   truthy, got false`.
10. `verification/regeneration_spec.spl` — 4/1. Generated-header text
    mismatch.
11. `verification/report_rendering_spec.spl` — 18/2. Summary / SDN
    state-count text mismatch.
12. `verification/unified_attrs_spec.spl` — 6/1. Emitted Lean theorem text
    mismatch.

## Caveat

The binary used self-identifies as *"this Rust-built Simple binary is a
bootstrap seed only; do not use it as the normal tool."* Items 3-6 in
particular are compiler-behaviour dependent and should be re-confirmed once a
full-CLI pure-Simple binary is deployed. Items 1, 2 and 7-12 are source-level
and will not change.

## Method / reproduction

```
for i in 1 2 3; do bin/simple test <spec> ; done
```

Read the `SPEC FILE VERDICT` line on **stdout**. Exit status is not a pass
signal — a run of `async/state_enum_spec.spl` exited 0 with the verdict only
on stdout, and piping through `tail` showed only stderr warnings and no
`Results:` line at all.

## Related

- `doc/09_report/skipped_flaky_test_census_2026-08-21.md` §5
- Daemon head-of-line blocking fix: `7a6f6459a81`

## Update 2026-08-21 — item 2 fixed; it was NOT a broken import in the sense filed

`verification/lean_workflow_spec.spl` went from **`executed=0`** to
**`9 total, 3 passed, 6 failed`**. Root cause of the zero-signal state: the spec
opened with `import io.fs as fs`, a module path that does not exist. Replaced
with `use std.nogc_sync_mut.fs.{exists, read_text, dir_delete_all}` and the two
call sites de-qualified (`fs.exist` -> `exists`, and note the product spelling is
`exists`, not `exist`). Both `test/01_unit/` and `test/unit/` mirrors updated.

A second, spec-side hygiene defect was fixed at the same time: the two temp-dir
examples reused fixed paths (`/tmp/simple-lean-workflow-{unit,strict}`) that a
previous run had already populated, so a re-run died with
`error[GenLeanUnmarkedOverwrite]` and then `array index out of bounds: index is
0 but length is 0`. Each now calls `dir_delete_all(temp_root)` first, which is
what turned that example's verdict from a harness artefact into a real content
assertion.

**The 6 remaining failures are genuine product defects, now visible for the
first time** (they were hidden behind `executed=0`). Handoff, with locations:

| example | failure | owner |
|---|---|---|
| flags unproven goals and formats them | `method is_model_complete not found on type LeanCheckResult` | `src/.../verification/lean/runner` |
| aggregates pass/fail and unproven counts | `method is_model_complete not found on type VerificationSummary` | same |
| extracts obligations with stable identifiers | `Module "verification.models" does not export 'ContractExprKind'` | `verification/models` |
| writes regenerated files to a temp directory | file written empty: `expected  to equal theorem demo : True := by rfl` — `regen.write_regenerated_files` | `verification/regenerate` |
| hard-fails on files that still contain sorry | `unknown extern function: _rt_process_run` (unbacked extern, same class as `unregistered_extern_silent_nil_2026-08-01.md`) | runtime/seed |
| flags missing validation targets as mismatches | `expected true to equal false` — `regen.validate_regeneration` | `verification/regenerate` |

Items 1 and 3-12 are unchanged and still OPEN.

# SFFI v2 authority group 4: silent audit failures + merge-clobbered hardening

Date: 2026-09-02
Gate: `push-sffi-v2-authority` / `scripts/check/check-sffi-v2-authority.shs`
Scope: `scripts/audit/{interpreter-eval-ast-sffi-authority,sffi-unsafe-backlog,test-codegen-quick-sffi-authority}.shs`

## Symptom

All three audits exited 1 with **zero output** (`set -eu` + bare `test`), so the
parent gate's `FAIL — 18 of 46 guard(s) failed` named no cause. While the gate is
RED every push in the repo uses `--no-verify`, bypassing all 19 push gates.

## Findings

### 1. `interpreter-eval-ast-sffi-authority.shs` — REAL violation (merge clobber)

Failing assertion: `test "$(grep -c '^@unsafe(' ast_ffi.spl)" -eq 29` — **actual 0**.

`9f4b24f41b1 fix(sffi): mark interpreter AST boundary unsafe` added 29
`@unsafe(reason: ..., capabilities: [ffi])` tags to
`src/app/interpreter/ffi/ast_ffi.spl`. `e274cd33719 chore: merge all
share-history worktree branches into main` reverted them. `git diff
9f4b24f41b1 HEAD -- ast_ffi.spl` is a **pure deletion** of exactly those 29
lines (0 added lines, 74 -> 74 non-`@unsafe` lines), i.e. a stale-snapshot
clobber, not intentional. The sibling file `eval_slice.spl` kept its
`unsafe(capabilities: [ffi]):` call blocks, so the boundary was left half-hardened.

Fix: restored the 29 tags from `9f4b24f41b1`. The expectation of 29 was NOT
touched — the source was wrong, not the number.

### 2. `test-codegen-quick-sffi-authority.shs` — REAL violation (same merge clobber)

Failing assertion: `test "$(grep -c '^extern fn rt_file_read_text' module)" -eq 0`
— **actual 1**.

`1b4edca296c SFFI v2 source-boundary hardening (#75)` replaced the raw
`extern fn rt_file_read_text` + `?? ""` fabricated-empty-source pattern in
`src/app/compile/test_codegen_quick.spl` with
`std.io_runtime.read_file_text_result` and an explicit `case Err(error)` arm.
`e274cd33719` reverted the file wholesale. Fix: restored `1b4edca296c`'s version.

### 3. `sffi-unsafe-backlog.shs` — NOT a ratchet; a swallowed dependency failure

This is a ledger emitter, not a frozen count. It ran
`scripts/audit/sffi-contract-inventory.shs ... >/dev/null 2>&1` under `set -e`,
so the dependency's failure killed it with no output. The real cause is the
inventory's own ratchet: `SFFI contract inventory: FAIL source_variants=416/399
migration=3359/3546` — 416 distinct source signatures against a frozen 399.

`sffi-contract-inventory.shs` is **not** its own row among the 46 guards, so the
backlog audit is the only thing surfacing that ratchet. It must therefore not be
decoupled. Fix: surface it explicitly as
`FAIL — ... dependency scripts/audit/sffi-contract-inventory.shs failed (rc=1): ...`
instead of silence. The 416/399 ratchet itself is **out of this change's scope**
(the inventory script is not one of the three audited here) and remains open.

## Verdict lines (unpiped `rc` captured on the line after each invocation)

Before (all three):
```
(no output)   rc=1
```

After:
```
PASS — 5 assertion(s) checked, interpreter AST SFFI authority: raw_declarations=29 unsafe_tagged=29 lexical_raw_calls=14 artifact_admission=absent   rc=0
PASS — 5 assertion(s) checked, quick codegen file-read authority: local_raw_declarations=0 result_lifts=1 codegen_calls=1 fabricated_empty_source=absent artifact_admission=absent   rc=0
FAIL — 1 assertion(s) checked, dependency scripts/audit/sffi-contract-inventory.shs failed (rc=1): SFFI contract inventory: FAIL source_variants=416/399 migration=3359/3546   rc=1
```

FAIL path proven by re-running the new audits against the pre-restore blobs:
```
FAIL — 5 assertion(s) checked, interpreter AST SFFI authority: unsafe_tagged_declarations expected 29, got 0   rc=1
FAIL — 5 assertion(s) checked, quick codegen file-read authority: local_raw_extern_declarations expected 0, got 1; result_lift_import expected 1, got 0; result_lift_call expected 1, got 0; error_arm expected 1, got 0   rc=1
```

All three now follow the `.claude/rules/vcs.md` convention: verdict LAST on
stdout, `PASS — <n> assertion(s) checked` / `FAIL — <expected vs actual>` /
`ERROR — nothing was checked (<reason>)`, exits 0/1/2. Non-vacuity is absolute:
a missing audited file, an empty contract inventory, or zero evaluated
assertions is ERROR (exit 2), never a pass.

## Parent gate

`sh scripts/check/check-sffi-v2-authority.shs`:
`sffi-v2-authority: FAIL — 16 of 46 guard(s) failed` (was 18). Sibling agents are
fixing the remaining rows concurrently.

## Open

- `scripts/audit/sffi-contract-inventory.shs` ratchet `source_variants=416/399`
  blocks `sffi-unsafe-backlog.shs`. Needs a separate owner: either the 17 new
  source-signature variants get tagged/migrated, or the ratchet is reviewed.

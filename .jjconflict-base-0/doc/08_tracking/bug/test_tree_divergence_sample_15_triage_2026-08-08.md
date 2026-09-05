# Test-tree divergence: 15-pair sample triage (2026-08-08)

**Status:** 2 pairs reconciled (real fixes, verified green/red/green). 1 pair
flagged as **CONTRADICTORY** (do not touch). 12 pairs classified, not touched.
Baseline file and divergence guard script were not modified.

## Context

`doc/08_tracking/bug/test_tree_divergence_982_diagnosis_2026-08-08.md`
established that `test/01_unit`/`test/unit` and `test/02_integration`/
`test/integration` are live duplicate trees with hundreds of independently
drifted pairs. This is a follow-up sample pass: 15 pairs spread across the
current diverged list (every ~65th entry of a 981-line sorted list, current
as of this run — one pair from the diagnosis's original 982 was reconciled by
another session in between), read from stable `git show origin/main:<path>`
snapshots (not the live, actively-clobbered working copy).

Command used to regenerate the list:
```
sh scripts/check/check-test-tree-divergence.shs
```
Verbatim tail:
```
check-test-tree-divergence: 5724 pairs compared, 4743 identical, 981 diverged
check-test-tree-divergence: baseline has 981 known-diverged entries
check-test-tree-divergence: diverged-path list written to /tmp/divergesample_scratch/current_diverged.txt
check-test-tree-divergence: PASS — 5724 pairs checked, 981 diverged (all baselined), 0 new, 0 stale-fixed
```

## The 15 sampled pairs

| # | Pair (label:relpath) | Diff size | Classification |
|---|---|---|---|
| 1 | `integration:app/app_mcp_intensive_spec.spl` | ~90 lines | **CONTRADICTORY** — see below |
| 2 | `integration:os/port/native_convergence_spec.spl` | 21 lines | Cosmetic/structural |
| 3 | `unit:app/formatter/formatter_comprehensive_spec.spl` | 1044 lines | Cosmetic/structural (both sides are dead — see below) |
| 4 | `unit:app/package/semver_spec.spl` | 48 lines | **REAL DIVERGENT CONTENT — FIXED** |
| 5 | `unit:app/ui/widget_modifiers_spec.spl` | 2 lines | Cosmetic (equivalent import path) |
| 6 | `unit:compiler/codegen/baremetal_method_dispatch_spec.spl` | 2 lines | Cosmetic (stale path in a comment only) |
| 7 | `unit:compiler/coverage/branch_coverage_7_spec.spl` | ~16 lines | Cosmetic (style rewrite, `!= nil`/`== nil` vs `.?`, same semantics) |
| 8 | `unit:compiler/parser/treesitter_visibility_spec.spl` | 2 pairs | Cosmetic (fixture body `0` vs `pass_dn`, same placeholder role) |
| 9 | `unit:lib/common/contracts/new_contracts_spec.spl` | 8 pairs | Real content lost but NOT fixed — see below |
| 10 | `unit:lib/common/pure/autograd_spec.spl` | 24 lines | Orphan-adjacent, flagged not fixed — see below |
| 11 | `unit:lib/crypto/aes128_gcm_nist_vectors_spec.spl` | 40 lines | **REAL DIVERGENT CONTENT — FIXED** |
| 12 | `unit:lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl` | 45 lines | Real content missing, flagged not fixed — see below |
| 13 | `unit:lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl` | 24 lines | Orphan-adjacent, flagged not fixed — see below |
| 14 | `unit:os/compositor/compositor_spec.spl` | 106 lines | Real content missing, flagged not fixed — see below |
| 15 | `unit:os/qemu_runner_extended_spec.spl` | 204 lines | Real content missing (stale paths + missing scenario), flagged not fixed — see below |

## CONTRADICTORY ASSERTIONS (most important finding — do not touch)

### `integration:app/app_mcp_intensive_spec.spl`

Both sides assert `expect(instances.len()).to_equal(100)` on the SAME loop,
but the loops iterate a different number of times because `..` is an
**exclusive** range in this language (`doc/07_guide/quick_reference/
syntax_quick_reference.md` line 1195, "Exclusive Range (`..`)").

Canonical (`test/02_integration/app/app_mcp_intensive_spec.spl:143`):
```
for i in 0..100:
    ...
expect(instances.len()).to_equal(100)   # line 151
```
100 iterations (0..99) → `instances.len() == 100` → assertion is correct.

Shadow (`test/integration/app/app_mcp_intensive_spec.spl:143`):
```
for i in 0..99:
    ...
expect(instances.len()).to_equal(100)   # line 151, UNCHANGED
```
99 iterations (0..98) → `instances.len() == 99` → the **same** assertion
(`== 100`) would now fail. This is the exact "off-by-one, one side wrong"
pattern already documented in the guard's own header comment for
`os/kernel/loader/app_registry_spec.spl` (`len()==19` vs `==18`).

The same `100 → 99` (and `50→49`, `500→499`, `200→199`) substitution recurs
at 8 more loop headers in the shadow copy (lines 166, 190, 211, 246, 273,
313, 337, 381), each paired with an assertion that was **not** updated to
match. Every one of these is a live discrepancy between the two copies'
actual pass/fail behavior for the same named test. **Per instructions, this
was reported only — neither side was edited or picked as "correct".** (The
canonical side's math is self-consistent; the shadow side's is not — but per
task rules that determination is not grounds to silently patch it here.)

The same diff also carries an unrelated, genuinely cosmetic change (a `tag:
["only-compiled"]` addition on the enclosing `describe`, a dict-literal key
quoting style change, and a shell-command flag drop) — those are structural,
not part of the contradiction.

## REAL DIVERGENT CONTENT — fixed (2 of 15, evidence below)

### 1. `unit:app/package/semver_spec.spl`

- Canonical (`test/01_unit/app/package/semver_spec.spl`) has 4 real `it`
  examples reading `src/lib/gc_async_mut/package/semver.spl` and
  `src/lib/gc_sync_mut/package/semver.spl` and asserting the presence of
  `version_equal`, `version_greater`, `parse_constraint`, `satisfies`, etc.
- Shadow (`test/unit/app/package/semver_spec.spl`) had been replaced (bulk
  "chore" commit `aff29a24dfe`, 2026-08-08) with a vacuous stub: `slow_it
  "skipped": val pending_reason = "variable 'ok1' not found - struct field
  access or scope issue"`.
- Verified before porting: `grep -n 'ok1'` on the canonical file returns
  **zero matches** — the stub's stated failure reason does not correspond to
  anything in this file's actual content, i.e. the stub-out reason looks
  fabricated/copy-pasted rather than a genuine per-file diagnosis. (Flagging
  this pattern — see "Process note" below.)
- Verified the target functions still exist: `grep -n "fn version_equal\|fn
  parse_constraint\|fn satisfies"` on `src/lib/gc_async_mut/package/
  semver.spl` — all present.
- **Fix applied:** ported the canonical file's content verbatim into the
  shadow file (both are now byte-identical, confirmed with `diff`).
- **Verification (binary: `build/native_probe/simple`, the only functional
  binary found in this environment — `bin/simple`'s symlink was missing and
  the deployed `release/x86_64-unknown-linux-gnu/simple` segfaults on any
  input right now, unrelated to this change; see "Environment note" below):**

  GREEN (after fix):
  ```
  Results: 4 total, 4 passed, 0 failed
  ```
  RED (sabotage: renamed `version_equal` → `version_equal_SABOTAGE` in one
  assertion string):
  ```
  Results: 4 total, 3 passed, 1 failed
  ```
  GREEN (reverted):
  ```
  Results: 4 total, 4 passed, 0 failed
  ```

### 2. `unit:lib/crypto/aes128_gcm_nist_vectors_spec.spl`

- Both copies have the same 12 `it` examples (NIST SP 800-38D Appendix B AES-128-GCM
  vectors, TC1-TC4). The divergence is inside 4 of the "corrupted tag is
  rejected" cases: the canonical copy asserts the actual rejection reason
  (`expect(msg).to_equal("authentication tag mismatch")`), the shadow copy
  had that assertion weakened to a vacuous `expect(true).to_equal(true)` (and
  the paired "unexpected Ok branch" `fail(...)` calls weakened to
  `expect(false).to_equal(true)` — behaviorally equivalent to `fail`, not a
  content loss, left as-is by the replace).
- **Fix applied:** replaced the 4 vacuous `expect(true).to_equal(true)` with
  the canonical `expect(msg).to_equal("authentication tag mismatch")`, and
  the 8 `expect(false).to_equal(true)` with the canonical `fail("unexpected
  AES-128-GCM vector result branch")` for parity (behaviorally identical,
  but now textually — and semantically for the msg case — matches the
  canonical file). Confirmed `diff test/01_unit/... test/unit/...` now
  returns empty (byte-identical).
- **Verification:** `bin/simple test` on this specific file returns "no
  parseable pass/fail summary in test output; refusing synthetic pass" on
  **both** the unmodified canonical copy and the shadow copy — a pre-existing
  harness issue unrelated to this edit (confirmed by running the untouched
  canonical file through the same command first). Used `simple run
  <spec>` instead, which executes the same `it` bodies and prints a real
  pass/fail summary:

  GREEN (after fix):
  ```
  12 examples, 0 failures
  ```
  RED (sabotage: changed one `expect(msg).to_equal("authentication tag
  mismatch")` to `expect(msg).to_equal("SABOTAGE-WRONG-MESSAGE")`):
  ```
  ✗ TC1 decrypt: corrupted tag is rejected
    expected authentication tag mismatch to equal SABOTAGE-WRONG-MESSAGE
  12 examples, 1 failure
  ```
  GREEN (reverted, and re-confirmed byte-identical to canonical):
  ```
  12 examples, 0 failures
  ```

## REAL DIVERGENT CONTENT — identified but NOT fixed (prioritized the 2 clearest per instructions)

- **`unit:lib/common/contracts/new_contracts_spec.spl`** — canonical has 8
  meaningful assertions (`expect("test_fn").to_equal("test_fn")`,
  `expect(100).to_be_greater_than(1)`, etc. — checking the literal arguments
  passed into `simple_contract_check`/`simple_contract_check_msg`); shadow
  has all 8 replaced with vacuous `expect true == true`. Not part of the
  "chore" stub-out pattern (no `pending_reason`), so likely a separate,
  deliberate simplification — needs its own review of whether the canonical
  assertions were ever meaningfully failing.
- **`unit:lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl`** —
  canonical has 3 extra `it` blocks (pixel-buffer read-back, `draw_text_bg`,
  `draw_text`) that shadow entirely lacks. Not fixed: touches
  `FramebufferDriver`/`BaremetalBackend`/`Engine2D` GPU/baremetal plumbing
  that the project's own memory notes flag as fragile (host GPU FFI pulled
  in via `Engine2D` struct fields) — higher risk to port confidently without
  board/QEMU verification in this session's time budget.
- **`unit:os/compositor/compositor_spec.spl`** — canonical has an entire
  extra `describe "Compositor maximize and restore":` block (2 `it` cases)
  covering window-state-machine geometry that shadow lacks, plus an extra
  `use common.ui.wm_window_state.{...}` import the shadow dropped. Not
  fixed: nontrivial state-machine assertions, deserves dedicated review.
- **`unit:os/qemu_runner_extended_spec.spl`** — real divergence but of a
  different character: the shadow copy references **paths that no longer
  exist** in the tree (`scripts/make_os_disk.shs`, `examples/simple_os/...`)
  while canonical uses the current paths (`scripts/os/make_os_disk.shs`,
  confirmed present via `ls`; `examples/09_embedded/simple_os/...`,
  confirmed present via `ls`). The shadow copy also omits an entire scenario
  (`scenario_arm64_desktop_engine2d`) and its marker-fragment helper that
  canonical imports and exercises. Not fixed: 204-line diff, large surface,
  needs a dedicated lane.

## Orphan-adjacent / stub-with-fabricated-reason (flagged, not deleted)

- **`unit:lib/common/pure/autograd_spec.spl`** and
  **`unit:lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl`** — same
  bulk-"chore"-commit stub pattern as semver_spec (`slow_it "skipped": val
  pending_reason = "..."`), but here the stated failure reason (`"function
  'add' not found in interpreter runtime"` / `"variable 'PATH_SEP' not found
  - struct field access or scope issue"`) is **plausible against this file's
  actual content** (`PATH_SEP` genuinely appears as a checked string literal
  in the canonical `baremetal_path_spec.spl`), unlike semver's stub. Given
  the uncertainty about whether porting would just reproduce a real
  interpreter failure, these were left as flagged candidates for a
  dedicated lane rather than blindly ported.

## Cosmetic / structural only (left alone)

- `integration:os/port/native_convergence_spec.spl` — same test, old-style
  `extern fn rt_env_get` + manual nil-check (shadow) vs `use
  std.io_runtime.{env_get}` (canonical) — functionally equivalent helper
  implementations, no assertion difference.
- `unit:app/formatter/formatter_comprehensive_spec.spl` — canonical is a
  4-line "skipped" stub; shadow is the same 4-line stub PLUS >1000 lines of
  `#`-commented-out dead test code. Neither side executes any real
  assertions today (`grep -vc '^#|^$'` on the shadow file returns 4). No
  live behavioral difference.
- `unit:app/ui/widget_modifiers_spec.spl` — import path
  `app.ui.render.html_widgets.{render_html_widget}` (canonical) vs
  `app.ui.render.widgets.{render_html_widget}` (shadow). Verified both
  resolve: `src/app/ui.render/widgets.spl:10` re-exports
  `render_html_widget` from `html_widgets.spl`. Equivalent.
- `unit:compiler/codegen/baremetal_method_dispatch_spec.spl` — a stale path
  in a `#` comment only (`examples/09_embedded/simple_os/...` vs
  `examples/simple_os/...`); no executable content differs.
- `unit:compiler/coverage/branch_coverage_7_spec.spl` — style rewrite of
  Option/Dict presence checks (`!= nil` / `== nil` → `.?` / `not ... .?`),
  same check, same expected outcome on both sides.
- `unit:compiler/parser/treesitter_visibility_spec.spl` — parser-fixture
  function bodies use `0` (canonical) vs `pass_dn` (shadow) as filler
  statements; both are syntactically valid no-op bodies for a parse-only
  test, no assertion differs.

## Environment note (2026-08-08, mid-session)

`bin/simple` (the pure-Simple self-hosted binary the repo's rules mandate as
default tooling) was unusable during this session: the `bin/simple` symlink
was missing (removed by a concurrent session's clobbering), `scripts/setup/
setup.shs` reported the release binary "not found — run bootstrap first",
and the release binary that did exist
(`release/x86_64-unknown-linux-gnu/simple`) segfaulted on **every** input,
including a one-line trivial spec with no repo dependencies — confirming
this was a binary-health problem, not a content problem. A working binary was
found at `build/native_probe/simple` (self-identifies as "Simple Test Runner
v0.8.1"); all verification runs above used it with `SIMPLE_MODULE_LIMIT=4000`
per this task's stated environment workaround. This is recorded here per the
repo's own rule ("Binary identity caveat" in `.claude/rules/testing.md`) —
findings above are attributable to `build/native_probe/simple`, not to
whatever `bin/simple` currently resolves to.

## Process note

The bulk "chore" commit `aff29a24dfe` (2026-08-08, "chore: align sspec and
coverage docs with queued updates") replaced at least 3 shadow-tree spec
files sampled here (`semver_spec.spl`, `autograd_spec.spl`,
`baremetal_path_spec.spl`) with `slow_it "skipped"` stubs carrying a
`pending_reason` string. For `semver_spec.spl` that reason does not match
anything in the file it was attached to (`ok1` appears nowhere in either
copy), suggesting at least one of these stub-outs used a fabricated or
mismatched justification rather than a genuine per-file failure diagnosis.
Given `aff29a24dfe` is titled as a docs/chore sync and actually replaced
live test assertions with skips, this matches the standing project note
"chore-labelled bulk commits hide semantic changes" — worth a wider audit of
what else that commit touched, out of scope for this sampling pass.

## Files changed this session

- `test/unit/app/package/semver_spec.spl` — real content ported from
  `test/01_unit/app/package/semver_spec.spl`, now byte-identical.
- `test/unit/lib/crypto/aes128_gcm_nist_vectors_spec.spl` — weakened
  assertions restored to match `test/01_unit/lib/crypto/
  aes128_gcm_nist_vectors_spec.spl`, now byte-identical.

Baseline file (`scripts/check/test_tree_divergence_baseline.txt`) was **not**
touched — both fixed pairs are still listed there; per the guard's own
design, the next run of `check-test-tree-divergence.shs` will report them as
"fixed-but-still-baselined" (`comm -13`), which is the correct signal for a
human to now shrink the baseline for exactly these 2 lines. That baseline
edit was intentionally left for a reviewer, not done here, since this task's
scope was the sample triage plus the fixes, not baseline maintenance.

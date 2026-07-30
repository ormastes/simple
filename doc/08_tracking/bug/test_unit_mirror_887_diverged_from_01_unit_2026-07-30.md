# Bug: `test/unit/` is a drifting mirror of `test/01_unit/` — 887 diverged files, all still executed by the default scan

- **Date:** 2026-07-30
- **Severity:** medium (structural — stale spec copies run in every full suite; fixes land in `01_unit` and silently don't apply to the mirror)
- **Area:** test tree layout / test runner scan root
- **Found by:** lane SPD1 (mission-critical robustness campaign), following lane LEXD's single-file finding.

## Numbers (2026-07-30 scan)

- `test/unit/`: 8,309 files; `test/01_unit/`: 14,654 files.
- Same-relative-path pairs: 8,291 (the other 18 are stale generated
  artifacts unique to `test/unit`: `.jit.note.sdn`, `summary.txt`).
- Byte-identical: 7,404 (89.3%). **Diverged: 887 (10.7%)** — 878
  `_spec.spl`, 9 `_test.*`.
- `bin/simple test`'s default scan root is `test/` recursive, so BOTH
  copies of every pair execute — diverged mirror copies run stale
  assertions (or fail outright: `inline_asm_core_parser_spec.spl` was
  6/10 in the mirror vs 10/10 in `01_unit` until reconciled this date).

## Caveat before acting in bulk

A sample of diverged pairs shares the same last git commit hash on both
sides — some "divergence" is concurrent uncommitted working-tree edits
from parallel lanes, not long-standing drift. Re-scan on a clean checkout
of origin/main before deciding a bulk policy. Ranked lists preserved in
the SPD1 lane report (top offenders: browser_session_fetch_wasm_chain,
browser_session, isel_riscv32/64, simple_web_renderer).

## Fix direction (needs a policy decision — orchestrator/user)

Either delete the `test/unit/` mirror entirely (after porting any
content genuinely newer on that side), or exclude it from the default
scan root, or make it a symlink. Until then: any spec repair applied
under `test/01_unit/` MUST check for and port to a `test/unit/` twin.

## Sampled RED census (lane MIRR1, 2026-07-30)

### Method

1. Recomputed the diverged set from scratch: `sha256sum` every file
   under `test/unit/**` and `test/01_unit/**`, joined by
   same-relative-path, compared hash. Result: **8,310 files in
   `test/unit/`, 14,675 in `test/01_unit/`, 8,292 same-path pairs, 884
   diverged** (875 `_spec.spl`, 8 other `.spl`, 1 `.js`). This
   **confirms** the previously-reported 887 to within measurement
   noise — the 3-file delta is consistent with reconciliations already
   landed since that scan (e.g. `bba83684c75`) plus normal churn in a
   shared, concurrently-edited working copy (multiple lanes active).
   18 files exist only under `test/unit/` (stale generated artifacts:
   `.jit.note.sdn`, `summary.txt` — not specs, excluded from sampling).
2. Sampled 25 of the 875 diverged `_spec.spl` paths **reproducibly**:
   sort the list, take every 35th entry starting at line 1
   (`awk 'NR==1 || (NR-1)%35==0'`), giving exactly 25 evenly-spread
   picks (not the first 25, not random-each-run).
3. Ran each of the 25 under **both** `test/unit/<rel>` and
   `test/01_unit/<rel>`:
   `env -u SIMPLE_TIMEOUT_SECONDS timeout 300 bin/simple test --no-session-daemon <spec>`,
   captured the `Results:` line from each log (50 runs total, all
   completed — no timeouts, no crashes, no NO-EXECUTE cases in this
   sample).

### Per-class table (n=25)

| Class | Count | % | Examples |
|---|---|---|---|
| MIRROR-STALE (mirror red, twin green) | 4 | 16% | `app/branch_coverage_3_spec.spl` (75/78 pass), `compiler/coverage/branch_coverage_17_spec.spl` (75/78), `compiler/tools/header_gen_spec.spl` (0/1), `lib/common/png_decode_deflate_spec.spl` (4/14) |
| BOTH-RED (real product defect) | 6 | 24% | `app/ui/backend_matrix_spec.spl`, `lib/common/compress_facade_harness_spec.spl`, `lib/editor/host_simpleos_surface_contract_spec.spl`, `os/drivers/real_device_readiness_spec.spl`, `os/qemu_runner_desktop_spec.spl`, `sffi/sffi_public_api_spec.spl` |
| COSMETIC (both green, content differs — extra/renamed examples, no failures either side) | 15 | 60% | `app/lsp/helper_functions_spec.spl`, `app/package/manifest_spec.spl`, `compiler/backend/native/encode_riscv64_spec.spl`, `compiler_core/exhaustiveness_spec.spl`, `compiler/lexer/lexer_spec.spl`, `lib/common/string_spec.spl`, `lib/std/concurrency/concurrency_spec.spl`, +8 more |
| MIRROR-AHEAD (mirror green, twin red) | 0 | 0% | none in sample |
| NO-EXECUTE (no `Results:` line either side) | 0 | 0% | none in sample |

Full 25-path sample list, per-file before-fix `Results:` lines for both
sides, and raw logs are preserved in the lane sandbox
(`/tmp/claude-1000/.../scratchpad/sample25.txt`,
`results_final.tsv`, `logs/*.log`) — not checked in.

Root cause seen in all 4 sampled MIRROR-STALE cases: the mirror is
simply an older revision of the same spec (older `use` import paths,
missing new test cases, or use of the known-broken `x.?` optional-check
operator that `01_unit` already replaced with `!= nil` — see memory
`reference_seed_exists_check_lowers_to_bool`). None were cases where
the mirror had unique-but-correct content; every diff was 01_unit
strictly ahead.

### Extrapolation (CAVEAT: 25-file sample, ±~20 points at this n)

Applying the per-class rate to the 875 diverged `_spec.spl` files:

| Class | Rate | Projected count / 875 |
|---|---|---|
| MIRROR-STALE | 16% | **~140** |
| BOTH-RED | 24% | ~210 |
| COSMETIC | 60% | ~525 |
| MIRROR-AHEAD | 0% | ~0 (not ruled out at larger n) |
| NO-EXECUTE | 0% | ~0 (not ruled out at larger n) |

**Caveat:** n=25 out of 875 is a ~2.9% sample; a binomial 95% CI on the
16% MIRROR-STALE rate is roughly 4%-36%, i.e. the true stale count
could plausibly be anywhere from ~35 to ~315. Treat "~140" as a
plausible order-of-magnitude, not a precise figure. The larger
takeaway that survives the wide interval: the mirror is **not** a
purely cosmetic problem — an estimated quarter of diverged pairs
(BOTH-RED) point at real product defects the mirror happens to also
exercise, and a meaningful double-digit-percent slice (MIRROR-STALE)
is pure mirror rot with no product-defect content, i.e. safe,
mechanical repair work once someone works through it.

### Repair log (4 of up-to-10 MIRROR-STALE specs from the sample; all 4 found in-sample were repaired)

Reconciled by copying the `test/01_unit/` twin over the `test/unit/`
mirror file, after reading both sides to confirm 01_unit was strictly
ahead (newer imports/API, more test cases, no unique mirror-only
content lost):

| Spec | Before (`test/unit/`) | After (`test/unit/`) |
|---|---|---|
| `app/branch_coverage_3_spec.spl` | 78 total, 75 passed, 3 failed | 78 total, 78 passed, 0 failed |
| `compiler/coverage/branch_coverage_17_spec.spl` | 78 total, 75 passed, 3 failed | 78 total, 78 passed, 0 failed |
| `compiler/tools/header_gen_spec.spl` | 1 total, 0 passed, 1 failed | 25 total, 25 passed, 0 failed |
| `lib/common/png_decode_deflate_spec.spl` | 14 total, 4 passed, 10 failed | 18 total, 18 passed, 0 failed |

Only 4 MIRROR-STALE specs turned up in the 25-file sample (the
"up to 10" budget was not the binding constraint here); all 4 were
repaired and re-verified green, byte-identical to their `01_unit`
twin post-repair. The remaining ~136 projected MIRROR-STALE specs
(875-file population) are unrepaired and would need either a wider
sample or a full pass to identify individually.

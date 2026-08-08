# Check Script Fail-Open Audit — 2026-08-08

**Scope:** Automated scan of all `scripts/check/**/*.shs` for fail-open patterns (absence read as evidence).

**Coverage:** 462 total .shs files; 458 analyzed (4 excluded: previously fixed).

---

## REVIEWER CORRECTIONS (2026-08-08, applied after spot-checking)

This section supersedes the framing below where they conflict. The raw scan is
useful; three of its conclusions are not safe to act on as written.

**1. "Skip→Green is the most dangerous pattern" is too strong. Most Pattern A
hits are optional-capability lanes, and exiting 0 there is a design choice, not
a defect.** Spot-checked: `build-mlkem-simd-c-lane.shs:105` (no SIMD backend on
host), `check-gpu-runnable.shs:21` (no simple binary), and
`check-engine2d-simd-c-kernels.shs:76` (no C compiler) are all real Pattern A
matches — and all three are lanes that genuinely cannot run everywhere. At least
**33 of the 57** Pattern A files are capability-gated (gpu / electron / macos /
simd / vulkan / metal / board / cuda / directx).

The actual defect is narrower and should be stated precisely: **a caller cannot
distinguish "ran and passed" from "did not run".** The fix is a distinct exit
code, not converting these to `exit 1` — a permanently-red job on hosts lacking a
GPU gets muted, which recreates the very problem being fixed.

**2. The report's `exit 77` recommendation invents a convention that does not
exist in this repo.** `/usr/bin/grep -rl 'exit 77' scripts/check/` returns **0
files**. (`build-mlkem-simd-c-lane.shs` *receives* 77 from a child process and
then exits 0 — it does not emit 77.) The convention that DOES exist here, used by
the pre-push guards and by `check-aot-lane-fences.shs`, is:

| exit | meaning |
|------|---------|
| 0 | PASS — ran and passed; verdict states what was checked |
| 1 | FAIL — ran and found a defect |
| 2 | ERROR — nothing was measured; NOT a pass |

Prefer extending this existing three-code scheme rather than introducing a
fourth. Adopting `77` would need a repo-wide decision and every caller updated.

**3. Confirmed false positive in the "top 10":
`check-gui-hardening-open-gates.shs:231` is fail-CLOSED, not fail-open.** It is a
`return 0` from a shell *function* that echoes `fail` — the string is the return
channel, the numeric 0 is not an exit code. It correctly refuses to run an
unbounded evidence command. Remove it from the high-risk list. Any other
`return 0` inside a function is subject to the same misreading and must be
re-checked before action.

**4. The Pattern B count (684) is an over-match and must not be quoted as a
defect count.** `[ -n "$var" ]` is an ordinary idiom; only the subset where an
EMPTY value causes an assertion to be skipped is a defect. That subset was not
isolated. Treat 684 as "lines matching a syntactic shape", not findings.

**Bottom line: the honest headline is not "851 fail-open bugs".** It is: ~57
scripts cannot signal "did not run" distinctly from "passed", of which most are
legitimately capability-gated, and the remedy is a shared skip/error exit
convention plus caller support. The four already-fixed AOT fences are the
template.

---

## Summary

| Pattern | Count | Risk | Description |
|---------|-------|------|-------------|
| **A: Skip→Green** | 57 | HIGH | `exit 0` on paths printing SKIP/NOTE/unavailable |
| **B: Empty Absorbed** | 684 | MEDIUM | `[ -n "$var" ]` guard where empty skips assertion |
| **C: Missing-Tool Skip** | 0 | HIGH | `command -v X \|\| exit 0` (tool absence = skip) |
| **D: Short Timeout** | 65 | MEDIUM | `timeout ≤300s` with generic catch-all, no `rc=124` branch |
| **E: Pipe $?** | 27 | LOW | `rc=$?` after a pipe (captures wrong exit code) |
| **F: Verdict/Exit Mismatch** | 18 | MEDIUM | Final `echo "PASS"` reachable without assertion |

**Total findings:** 851 (many are overlapping or low-confidence; ~66 HIGH/MEDIUM after dedup)

---

## Per-Pattern Detailed Findings

### Pattern A: Skip→Green (57 high-risk findings)

These are the most dangerous: a script prints SKIP but exits with code 0, causing CI and log parsers to read "green" / "passed" when the test was not actually run.

**Top 10 findings (ranked by gate importance):**

| File | Line | Snippet | Fix |
|------|------|---------|-----|
| `build-mlkem-simd-c-lane.shs` | 105 | `echo "MLKEM_SIMD_C_LANE: SKIP"` + `exit 0` | Return `exit 77` or exit-code that signals skip |
| `check-gpu-runnable.shs` | 21 | `echo "gpu_runnable_gate=skip"` + `exit 0` | Use `exit 77` or dedicated skip exit code |
| `check-engine2d-simd-c-kernels.shs` | 76 | `echo "SKIP: no C compiler found"` + `exit 0` | Change to `exit 1` if tool is required |
| `check-electron-vulkan-web-parity.shs` | 38 | `echo "SKIP: electron not installed"` + `exit 0` | Use `exit 77` for optional dependencies |
| `cert/sanitizer-matrix.shs` | 262 | `row "$_kind" seed SKIP "Rust nightly"` + `exit 0` | Return `exit 77` from `row()` function |
| `cert/sanitizer-matrix.shs` | 267 | `row "$_kind" runtime SKIP "no C compiler"` + `exit 0` | Check: is C compiler required or optional? |
| `cert/freeze-tool-qual-golden.shs` | 144 | `printf 'NOTE: ...'` + `exit 0` | Use `exit 77` or change to WARNING/non-fatal |
| `check-cpu-simd-engine2d-evidence.shs` | 475 | `echo "...: skip (no Engine2D)"` + `exit 0` | Return `exit 77`; verify Engine2D is optional |
| `check-electron-live-smoke.shs` | 114 | `write_report skipped SKIP_*` + `exit 0` | Check `write_report` function for skip vs pass |
| `check-gui-hardening-open-gates.shs` | 231 | `echo "timeout command unavailable"` + `exit 0` | `timeout` is often required; return `exit 1` |

**Risk assessment:**
- **Gate criticality HIGH:** Anything gating a promotion or release should fail (not skip) if a required tool is missing.
- **Gate criticality MEDIUM:** Optional hardware/platform gates (GPU, Metal, Electron) can skip; use `exit 77`.
- **Ambiguity:** Many scripts do not document whether missing dependencies should skip or fail. Requires per-gate review.

---

### Pattern B: Empty Absorbed (684 findings)

These are common but lower-risk because they often represent intentional defaults:

```sh
[ -n "$var" ] && [ "$var" != unassigned ] || return 1  # empty var → return 1 (fail)
if [ -n "$PINNED_COMPILER" ]; then ...                 # empty → skip block (sometimes OK)
if [ -z "$MODE" ]; then echo "error"; exit 1; fi       # empty → fail (correct)
```

**High-risk subset:** About 40-50 cases where an **empty** value silently skips a critical assertion (not a default path). These need manual review per file.

**Example false positive:** `[ -n "$clean_name" ] && printf ...` — this is a guard for optional output, not an assertion skip.

---

### Pattern D: Short Timeout (65 findings)

Timeouts ≤300s often lack explicit handling for the timeout exit code (124). A timeout that falls into a generic `else` branch becomes an unrelated defect report.

**Example:**

```sh
timeout 10 "$binary" --version >/dev/null 2>&1 || return 0  # ✓ correct (exit 0 on fail)
timeout 30 some_long_test 2>&1                              # ✗ unclear: what if rc=124?
if timeout 60 cmd; then echo PASS; else echo FAIL; fi      # ✗ timeout → FAIL (wrong signal)
```

**Top cases:**
- 23 instances of `timeout 10` (version checks — usually safe as `|| return 0`)
- 12 instances of `timeout 20` / `timeout 30` (work-unit timeouts — risky)
- 8 instances of `timeout 60` (dangerous: 1-minute limit on heavy work)

**Fix pattern:** Add explicit:
```sh
timeout 30 work || rc=$?
if [ $rc -eq 124 ]; then echo "TIMEOUT"; exit 1; fi  # or 77 if skip
```

---

### Pattern E: Pipe $? (27 findings)

Capturing exit code after a pipe loses the first command's status:

```sh
cmd1 | cmd2 | cmd3 ; rc=$?  # ✗ gets exit code of cmd3, not cmd1
```

**All 27 are in log-parsing or test-output contexts** — most are LOW risk because the actual assertion is the log parse result, not the original exit code. **But verify the intent in each.**

---

### Pattern F: Verdict/Exit Mismatch (18 findings)

Scripts with a final `echo "... PASS ..."` line reachable even when assertions were skipped.

**Example:** `check-expect-footgun.shs:81` — `exit 0` after `echo "REPORT-ONLY: found X footguns"`. The `--strict` flag allows exit 1 for real failures, but the **default** is silent-pass on any findings, which is the opposite of a "fail on findings" assertion.

**Risk:** MEDIUM for most (these are intentional report-only lanes). **HIGH for any that claim "PASS" after a skip.**

---

## Recommendations (Prioritized)

### Immediate (Week 1)
1. **Pick Pattern A hotspots:** Review the 10 HIGH files above. Decide for each:
   - Is missing dependency a **FAIL** (critical) or **SKIP** (optional)?
   - If SKIP: change `exit 0` to `exit 77`.
   - If FAIL: change message from SKIP to FAIL and keep `exit 1`.

2. **Audit Pattern B subset:** ~40–50 cases where empty var causes assertion skip (not a default). File a bug per case if unclear.

### Near-term (Week 2–3)
3. **Add timeout handling:** For any `timeout 20+`, check if `rc=124` needs dedicated handling. Add explicit branch if missing.

4. **Verify Pattern F:** Confirm report-only scripts are intentionally passing. Add doc comments explaining the skip semantics.

### Long-term
5. **Add pre-push validation:** A hook like `check-no-conflict-markers-push.shs` that rejects a commit with bare `exit 0` following SKIP output.

6. **Standardize skip semantics:** Define org-wide: is skip `exit 0` (CI-friendly) or `exit 77` (test-framework convention)?

---

## Coverage & Methodology

**Scanning method:**
- `/usr/bin/grep` (not the aliased `grep`) to bypass `.gitignore`.
- Pattern searches for literal strings: `SKIP`, `SKIPPED`, `NOTE`, `unavailable`, `not found`, `not pass`.
- Guard patterns: `[ -n "$var" ]`, `[ -z "$var" ]`, `command -v`, `timeout`, pipe-into-`$?`.
- Result: 851 raw matches; ~66 after filtering duplicates and obvious false positives.

**False positives excluded:**
- `SKIP_*` variable names (e.g., `SKIP_ELECTRON_LIVE_SMOKE`).
- Comments and doc strings.
- Functions like `row()` that wrap skip logic (harder to trace without execution).

**Known limitations:**
- Did not execute scripts (load is high; multi-minute native builds).
- Pattern B (684 findings) has ~600 false positives (guards for optional output, not critical assertions).
- Multi-line patterns (e.g., skip in a function, `exit 0` 20 lines later) may be missed by simple line-proximity checks.

---

## Files Scanned

Total: **462 .shs files**  
Analyzed: **458** (4 excluded per request)  
Excluded: `check-native-object-cache-granularity.shs`, `check-rt-io-file-native-jit-stub.shs`, `check-native-option-bool-llvm-verify.shs`, `check-native-utf8-slice.shs`

---

## Appendix: Raw Pattern Counts (Grep Commands Used)

All searches used `/usr/bin/grep -rn` on `scripts/check/`:

```bash
# Pattern A (SKIP-then-exit-0):
/usr/bin/grep -rn 'SKIP\|SKIPPED\|NOTE' scripts/check --include="*.shs" | \
  /usr/bin/grep -v 'SKIP_' | wc -l
# Result: 57 potential matches after filtering

# Pattern B (empty variable absorbed):
/usr/bin/grep -rn '\[ -n "\$' scripts/check --include="*.shs" | wc -l
# Result: 684

# Pattern C (missing tool as skip):
/usr/bin/grep -rn 'command -v.*|| *{.*exit 0' scripts/check --include="*.shs" | wc -l
# Result: 0 (no exact matches with `{ ... exit 0 }` on same line; multi-line cases present)

# Pattern D (timeout <= 300):
/usr/bin/grep -rn 'timeout [0-9]\{1,3\}[^0-9]' scripts/check --include="*.shs" | wc -l
# Result: 65

# Pattern E (pipe rc=$?):
/usr/bin/grep -rn 'rc=\$?' scripts/check --include="*.shs" | wc -l
# Result: 27

# Pattern F (exit 0 after verdict):
/usr/bin/grep -rn 'exit 0' scripts/check --include="*.shs" | wc -l
# Result: 250+ (too many to be all verdict mismatches; 18 reviewed)
```

---

**Report generated:** 2026-08-08  
**Audit method:** Automated pattern scanning + manual spot-checks  
**Next audit:** After fixes land to verify remediation

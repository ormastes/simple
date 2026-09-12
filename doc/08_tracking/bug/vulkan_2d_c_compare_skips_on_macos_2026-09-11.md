# `check-vulkan-2d-c-compare.shs` always reports `compare_status=skipped` — two independent causes

**Status:** Cause 1 RESOLVED 2026-09-12; Cause 2 OPEN (host blocker). See the 2026-09-12 section at the end.

Measured 2026-09-11 on macOS (Apple M4), at `origin/main` = `75b81c1d1f0` (#528 merge; #529/#530 not present at fetch time).

## Cause 1 (structural, not host-specific): aggregate() never sees `c_st=admitted`

`scripts/check/check-vulkan-2d-c-compare.shs:249-254` (`aggregate()`) requires
`c_st = admitted` and `s_st = admitted` to proceed to a ratio comparison
(lines 216, 223). But the main run body only ever assigns
`c_status=measured-unadmitted` (line ~697, `c_reason=receipt-needs-common-admission`)
after a fully successful live C measurement — it never assigns `c_status=admitted`
anywhere. So even a leg that measures perfectly cleanly reports
`compare_status=skipped compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`
unconditionally. This reproduced on this host: the C leg built, ran against
real MoltenVK, and reported a clean contract
(`c_line=c-vulkan-2d ... p50_ns=436000 p95_ns=1060000 ... device_vendor=106b device_id=1a040209`),
and the run still emitted `compare_status=skipped` for this reason alone —
run manifest: `build/vulkan-2d-c-compare/runs/run-20260911T060740Z-64492/`.
A separate common-admission step (not present in this script) is required
before `compare_status` can ever be `pass`/`fail` via the default invocation.
This is fail-open by design per the script's own header (line 30: "Exit: 0
when aggregate is pass or **skipped**") — confirmed empirically, `rc=0`.

## Cause 2 (this host): seed-detector rejects the only deployed self-hosted binary

`scripts/check/check-vulkan-2d-c-compare.shs:739-740`:
```
elif [ -L "$SIMPLE_BIN" ] || simple_binary_is_seed "$SIMPLE_BIN"; then
    simple_reason=bootstrap-seed-forbidden
```
`simple_binary_is_seed` (lines 198-204) matches the deployed macho binary
`/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple` via its
`strings`-based check: that binary literally embeds the text
`"WARNING: this Rust-built Simple binary"` (a runtime warning banner) plus
`compiler_rust/target` path strings, matching two of the three alternations
at line 201 (`rust-built Simple binary`, `compiler_rust/target`). The binary
is genuinely a Rust-seed-class artifact (`--version` reports
`Simple v1.0.0-rc.1`, no self-hosted-CLI marker) — this attribution is
correct, not a false positive to bypass. This repo has **no self-hosted
(pure-Simple) `bin/simple` deployed on this macOS host**, only the Rust seed.

In this worktree's default invocation (no `SIMPLE_BIN` override, no deployed
`bin/simple` at all), the Simple leg instead skips one step earlier via
`no-selfhosted-simple-binary` (line 737, `[ ! -x "$SIMPLE_BIN" ]`) — either
way the Simple leg never reaches `admitted`.

## Resume command for a self-hosted host

Once a genuinely self-hosted (pure-Simple, non-seed) `bin/simple` is deployed
(no `WARNING: this Rust-built Simple binary` string, no `compiler_rust/target`
path strings, not a symlink into the seed tree):
```
SIMPLE_BIN=/path/to/self-hosted/bin/simple \
  sh scripts/check/check-vulkan-2d-c-compare.shs
```
This still will not flip `compare_status` past `skipped` until Cause 1 above
is also fixed (the admission step that promotes `measured-unadmitted` to
`admitted` needs to be wired into this script, or `aggregate()` needs to
accept `measured-unadmitted` as sufficient for a same-host comparison).

## No bypass taken

Per instructions, the tracked script was not edited to route around the
seed-detector or the admission requirement. The comparison row for this run
was produced manually (same workload: 800x600, 64 rects, 300 frames, 5
warmups, both legs against the same MoltenVK ICD) — see
`doc/10_metrics/ui/vulkan_2d_c_vs_simple_compare_macos_2026-09-11.md`,
`mode=manual`.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

## 2026-09-12 (Lane 4) — Cause 1 RESOLVED, plus two more structural defects

Measured on Apple M4 at `origin/main` = `b9667d6584f`.

### Cause 1 is fixed, and it was four defects, not one

1. **The admission step was gated behind the status it produces.** `aggregate()`
   only calls `perf_compare_admit_env` once BOTH legs already read `admitted`,
   and nothing ever assigned `admitted` — the only terminal success state was
   `measured-unadmitted`. Fixed by adding **`perf_compare_admit_leg`** to
   `scripts/check/lib/perf-comparison-admission.shs`: a per-leg admission that
   performs exactly the SINGLE-SIDED checks the pairwise function already
   performed (projection schema, `fallback_state=none`, gpu identity, checksum
   charset, source/binary/receipt/artifact binding, seed refusal). The cross-leg
   equality checks stay in `perf_compare_admit_env` and are NOT weakened, and
   `measured-unadmitted` was not renamed.
2. **`perf-binary-admission-v1` had a validator and no producer anywhere in the
   repo** — one grep hit, the validator. Every row therefore carried an empty
   `binary_admission_path`/`sha256` and could only ever answer
   `invalid-<side>-binary-admission`. Added
   `perf_compare_write_binary_admission`, called only after that leg's own
   live-contract checks pass, bound to the exact measured binary hash.
3. **`unexpected-key-status` (found while fixing the above).** The live path
   built its rows with `sed 's/^c_/c_/p'`, which copies the consumer keys
   `status`/`reason`/`p95_ns` into a row whose validator accepts exactly 21
   projection keys. Even with both legs admitted this alone forced
   `compare_reason=admission-invalid-left-row:unexpected-key-status`. The live
   path now derives a proper projection via `project_row`, exactly as the
   `--aggregate` path does, while the durable `c.env`/`simple.env` keep the
   consumer keys the replay path reads back.
4. **Pre-publication path hashing (same discovery).** Rows name
   `$FINAL_RUN_DIR/...` paths that do not exist until
   `perf_immutable_publish_run` runs at the very end, so hashing them mid-run
   answers `stale-binary` for a perfectly good binary. Admission now runs against
   `*.env.admit` rows that are byte-identical apart from naming the staged files
   actually on disk; the published rows stay authoritative for `--aggregate`.

### Result on this Mac, C leg at 800x600 / 64 rects / 300 frames

```
c_status=admitted
c_reason=admitted
c_binary_admission_sha256=bc6e337a8311357c382abfa095729311273293a6ed77818bfa729e05bd290d4a
compare_budget_x1000=2000
compare_status=skipped
compare_reason=simple-leg-skipped:no-selfhosted-simple-binary
```

`sh scripts/check/check-vulkan-2d-c-compare.shs`, rc=0; run dir
`build/vulkan-2d-c-compare/runs/run-20260912T064931Z-65971`. The C leg measured
`p50_ns=474000 p95_ns=1087000` against real MoltenVK, `device_vendor=106b
device_id=1a040209`.

**The C leg now reaches `admitted` honestly.** A real `compare_status=pass|fail`
row still cannot be produced on this host, and that is Cause 2, not Cause 1:
there is no self-hosted (non-seed) `bin/simple` deployed here, and the seed
detector's refusal of the seed-class binaries that ARE here is correct. No
seed-mode Simple leg was added to route around it. The resume command above is
unchanged; Cause 1 no longer blocks it.

### Specs

`test/01_unit/scripts/perf_compare_leg_admission_spec.spl` (3/3 PASS) over
`test/01_unit/scripts/perf_compare_leg_admission_contract_test.shs`, which runs
with no GPU/ICD/Vulkan. Sabotage triple, each refused with its own named reason:
`TAMPERED_BINARY=unadmitted:stale-binary`,
`NO_RECEIPT=unadmitted:invalid-binary-admission` (the state every row was in
before this change), `WRONG_KIND=unadmitted:invalid-binary-admission`. The
generalizing example reads the tracked gate and fails if `aggregate` stops being
fed the stage-path rows.

### Sibling defect, NOT fixed here (not Lane 4)

`scripts/check/check-chrome-simple-web-comparison.shs:168` sources the same
helper and has the identical shape: no receipt producer, pairwise admission
gated behind `admitted`. The new `perf_compare_admit_leg` /
`perf_compare_write_binary_admission` are available to it; wiring them is that
lane's call. `test/03_system/check/perf_comparison_admission_contract_spec.spl`
re-run after the helper change: 11/11 PASS, no regression.

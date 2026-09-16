# guard_wiring_optout.txt carries a family of FALSE exemptions, several hiding RED gates

- **Date:** 2026-08-06
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Scope:** `scripts/check/guard_wiring_optout.txt`
- **Predecessor:** `doc/08_tracking/bug/core_c_capsule_gate_wrongly_opted_out_of_guard_wiring_2026-08-06.md` (`ed9e6f401f6`)

## Summary

`scripts/check/check-guard-wiring.shs:158-164` suppresses the wiring requirement
for every basename listed in `guard_wiring_optout.txt`. A listed gate is
therefore run by nothing at all — and an unreached check reports nothing, which
is indistinguishable from a passing one.

Line 22 exempted the core-C capsule gate as a *"hardware/emulator lane; needs
QEMU, an FPGA or a physical dev board."* That was false — the gate needs only
`cc`, `ar` and `nm` — and it had been RED at `origin/main` the entire time.

This audit asked how many other entries are false. **The answer is: at least 20
— 10 whose gate is GREEN, 8 whose gate is RED, and 2 worse than RED because they
are fail-open.** 23 reason texts were corrected in total; the other 3 name a real
dependency that the old text got wrong (a live HTTP endpoint, a missing driver
argument, a disk-reclamation report that is not a gate at all), which is a wrong
reason rather than a false exemption.

## The family, enumerated

360 entries. Only **6 templated reason strings** cover 347 of them, so this is
not 360 independent claims — it is 6 bulk classifications plus 13 hand-written
ones.

| # | Stated reason (verbatim prefix) | Makes an environment claim? |
|---|---|---|
| 127 | `orphaned at the 2026-08-01 wiring audit; not yet triaged` | No — honest by construction |
| 80 | `GPU/rasteriser evidence producer; needs a real GPU or display` | Yes |
| 62 | `browser/Electron runtime evidence producer; needs a real browser and display` | Yes |
| 59 | `hardware/emulator lane; needs QEMU, an FPGA or a physical dev board` | Yes |
| 10 | `platform-specific lane; needs a host OS this CI does not provide` | Yes |
| 9 | `performance measurement; results are machine-dependent` | Partly |
| 13 | individually hand-written | Varies |

The 127 "not yet triaged" entries make no environmental claim and so cannot be
*false* in the capsule sense. They remain debt. **211 entries make a testable
environment claim** and were the audit target.

**No STALE entries.** Every one of the 360 basenames resolves to a file in the
guard set (444 guards under `scripts/check/`, `scripts/audit/`, `scripts/*.shs`).
`check-guard-wiring.shs` independently confirms this: `0 bad opt-out(s)`.

## Method

1. Fingerprinted all 211 environment-claiming entries for whether the script
   *invokes* the claimed resource (`qemu-system-*`, `ssh`/`scp`, `$DISPLAY`/
   `xvfb-run`, `bun`/`node`/`electron`/`npx`, `nvcc`, vulkan, `uname` gating)
   versus merely mentioning it. **132 invoked nothing of the kind.**
2. **Ran 129 of those 132** on a plain Linux host (150s timeout, 6-way parallel),
   recording exit code, elapsed time and output. 3 were withheld as
   repo-mutating (below). Result: **33 exit 0, 90 exit 1, 2 exit 2, 4 timeout.**
3. Classified from the run output, not the fingerprint.

## Verdicts

### FALSE EXEMPTION, gate is GREEN (10)

Ran to a real verdict on a plain Linux host with base tools only. No capability
reason existed for any of them to sit outside CI.

| Gate | Time | Verdict line |
|---|---|---|
| `check-engine2d-row-scheduling.shs` | 1s | `engine2d_row_scheduling=true` |
| `check-llm-dashboard-live-http-setup-contract.shs` | 0s | `STATUS: PASS checked_count=8` |
| `check-nvme-baremetal-wrapper-coverage.shs` | 0s | `STATUS: PASS blockers=none` |
| `check-riscv-rtl-truth.shs` | 3s | `riscv_rtl_truth_ok=true, unknown=0` |
| `check-runtime-rocm-provider.shs` | 0s | `runtime_rocm_mock=pass` (it exercises the MOCK) |
| `check-simpleos-boundary-formal-proofs.shs` | 0s | `STATUS: PASS` |
| `check-simpleos-compiler-language-formal-proofs.shs` | 1s | `STATUS: PASS` |
| `check-simpleos-memory-safety-formal-proofs.shs` | 1s | `STATUS: PASS lean-proof-check project` |
| `check-simpleos-storage-formal-proofs.shs` | 0s | `STATUS: PASS` |
| `check-simpleos-ui-policy-formal-proofs.shs` | 1s | `STATUS: PASS` |

None of these needs QEMU, an FPGA, a board, a GPU, a display or a browser.
Five of them are *formal-proof artifact checks* — text over checked-in proof
files.

**Toolchain re-test (the second-pass correction).** This dev host has
`lean`, `lake`, `yosys` and `sby` installed, so "ran green here" could have meant
"quietly used a toolchain a checkout-only runner lacks" — the same error shape as
the `nvcc` case. Every entry above was therefore re-run with `~/.elan/bin` and
`~/.local/bin` stripped from `PATH`. **All ten still pass**, including the five
`*-formal-proofs.shs` gates (`STATUS: PASS`) and `check-riscv-rtl-truth.shs`.

**One entry failed that re-test and was corrected a second time:**
`check-simpleos-mission-critical-prereqs.shs` exits 1 with
`STATUS: FAIL simpleos-mission-critical-prereqs missing=sby,yosys`. Its hardware
reason was false, but so was the first correction — it genuinely needs the
SymbiYosys formal toolchain. Its entry now says so.

Two entries counted in an earlier draft are deliberately **not** counted as
false exemptions: `check-keyword-identifier-bindings.shs` (its reason was
honest and named its own precondition — see "Fixed in this change") and
`qemu-storage-audit.shs` (a disk-reclamation report, not a gate at all; its
reason was wrong but a non-gate cannot be a falsely-exempted gate).

### FALSE EXEMPTION, gate is RED (8) — the capsule incident class

These are the finding. Each claims hardware it does not use, each runs in
seconds on a plain host, and each is **currently failing** with nothing running
it.

| Gate | Time | Failure |
|---|---|---|
| **`check-simpleos-critical-formal-proofs.shs`** | 1s | `FAIL verification/kernel_capabilities -- contains 1 proof trust bypass(es) outside comments` |
| `check-riscv-formal-dual-track.shs` | 0s | `STATUS: FAIL riscv-fpga-sidecar-contract self-test` (its OWN self-test) |
| `check-simpleos-byl-sby-artifacts.shs` | 0s | `STATUS: FAIL riscv-fpga-sidecar-contract self-test` (same shared self-test) |
| `check-riscv-fpga-simpleos-preflight.shs` | 0s | `dual_arch_preflight_failures=8` |
| `check-riscv-rtl-sby-proof.shs` | 13s | `STATUS: FAIL reason=sidecar-contract-failed` |
| `check-llm-dashboard-evidence.shs` | 14s | `STATUS: FAIL llm-dashboard-evidence` |
| `check-llm-dashboard-live-evidence.shs` | 17s | `failures=dashboard_evidence,live_http_authenticated_read` |
| `check-engine2d-nomirror-fast-render-evidence.shs` | 13s | harness assertion failure |

**`check-simpleos-critical-formal-proofs.shs` is the most serious.** A gate whose
entire job is to detect *proof trust bypasses* is red on a real bypass in
`verification/kernel_capabilities`, was labelled as needing an FPGA, and had
therefore never run. Needs a SimpleOS proofs owner.

The two `riscv-fpga-sidecar-contract self-test` failures are one shared root
cause across three gates — fixing the sidecar contract self-test clears all
three. Needs a riscv owner.

### FAIL-OPEN, worse than RED (2)

Both exit **0** while checking nothing. Do NOT wire either as-is — wiring a
fail-open gate manufactures a green signal.

- **`check-simple-web-browser-conformance-contract.shs`** — exits 0 printing
  `simple_web_browser_conformance_executed_case_count=0`,
  `status=not-run`, `contract=pass`. It passes having run zero cases.
- **`qemu-frozen-source-admission.shs`** — exits 0 having printed **nothing at
  all**: no verdict line, no count, no output whatsoever.

### Additional fail-open found in passing (1)

- **`check-cuda-generated-2d-readback.shs`** exits **0** while its own comparison
  disagrees:
  ```
  cuda_generated_2d_readback_expected_pixels_sha256=4c069b7d6766874169ddb727de0a7e63b7651aa9b91f63b08c95a00433c76ab0
  cuda_generated_2d_readback_actual_pixels_sha256=2a08b7e9b3c66478c6951a6b6bd7356cf9c5b99a733c61d43aeb123db5abea8a
  ```
  Its exemption (`needs a real GPU`) is GENUINE — it reached `nvcc` at
  `/usr/local/cuda-13.0/bin/nvcc`. But the gate reports success on a mismatch.
  Needs a GPU owner.

### WRONG REASON CLASS, not wirable in a checkout-only job (~20)

`hardware/emulator lane` applied to scripts that need a **built `bin/simple` +
LLVM**, not an emulator. Representative:
`check-bootstrap-nonentry-module-global.shs` (`test -x bin/simple`, then
`native-build --backend llvm`; exits 1 silently with no output at all when the
binary is absent — itself a contract violation). These are false *reasons* even
though they cannot be wired here.

### NEEDS A DRIVER, not hardware (1)

- `check-simpleos-x86-kernel-elf.shs` — takes an ELF path or `--self-test`; with
  no argument it exits 1 at usage without reaching an assertion. Same shape as
  the already-honest `check-sspec-count-truthful.shs` entry.

### GENUINE (the large majority of the 211)

Backed by attempted runs:

- **`bun`/`node`/`electron` lanes** (~54 candidates): every one stops at
  `simple_web_engine2d_js_simple_bin_status=forbidden` /
  `..._source=repo-self-hosted-fallback-rust-seed-forbidden` — they require a
  self-hosted `bin/simple` plus a JS runtime.
- **CUDA lanes** (4): reach `nvcc`; genuinely need a GPU toolchain.
- **Vulkan lanes** (9+): reach vulkan tooling.
- **QEMU lanes**: e.g. `check-ai-cli-qemu-lanes.shs` exits 1 with
  `reason=missing-runtime-or-guest-serial-evidence`;
  `check-arm64-virtio-input-preflight.shs` reports `qemu_launched=false`.
- **macOS lanes**: `check-macos-metal-2d-live-evidence.shs` exits 1 with
  `FAIL (requires-macos)` in 0s — the reason is exactly right.
- **Container lane**: `check-docker-memory-cap.shs` needs docker/podman.

### UNKNOWN — not determined (7)

Not classified; stated here rather than guessed.

- **Timeouts at the 150s cap (4):** `check-hda-qemu.shs` (166s),
  `check-simpleos-mission-critical-release.shs` (150s),
  `check-simpleos-x86-64-wm-render-event-evidence.shs` (174s),
  `check-web-baremetal-size-audit.shs`.
  A timeout is not evidence of a hardware requirement.
- **Withheld as repo-mutating (3):** `check-renderdoc-browser-egl-hang-stack.shs`,
  `check-simpleos-formal-coverage.shs`,
  `check-simpleos-formal-setup-contract.shs` — each contains
  `git`/`jj` write commands and was not run in a shared working copy with ~10
  concurrent sessions. Two are base-tools-only and are the likeliest remaining
  false exemptions; they need a run in an isolated worktree.

## Fixed in this change

1. **`check-keyword-identifier-bindings.shs` wired.** Its opt-out reason was
   honest and named its own precondition (*"prints a bare OK with no count,
   which violates the guard contract. Add a count of files checked, then
   wire."*). The count is added, along with an ERROR exit and a ≥500-file
   vacuity floor; the opt-out entry is removed and the gate is wired into
   `repo-hygiene.yml` → `code-idiom-gates` in the same commit, as a stale entry
   would also fail the checker.

   - Live: `check-keyword-identifier-bindings: PASS — 34480 .spl file(s) checked`
   - Non-vacuous: with a `val match = 1` `.spl` staged into a scratch
     `GIT_INDEX_FILE` it reports
     `check-keyword-identifier-bindings: FAIL — 34480 .spl file(s) checked, 1 violation(s)`
     and exits 1.
   - Wiring live: `check-guard-wiring.shs` reports
     `444 guard(s) checked, 22 unwired, 0 bad opt-out(s)` — unchanged at 22,
     which proves the removal and the wiring landed together (a bare removal
     would have made it 23).

2. **`check-bun-web-render-bitmap-evidence.shs` path fix.** It did
   `exec sh scripts/check-node-web-render-bitmap-evidence.shs`; the delegate
   lives at `scripts/check/`. The script exited 2 with `cannot open ...: No such
   file` before reaching a single assertion. Found by running it — the first
   time anything ever had. After the fix it reaches its real precondition
   (`js_web_render_bitmap_simple_bin_status=forbidden`).

3. **23 exemption reasons corrected** in `guard_wiring_optout.txt`, each with the
   run evidence quoted inline. Reason text is free-form (the checker only
   enforces `NF>=2`), so this carries no wiring risk. No entry was removed to
   make anything green, and no gate was weakened.

## Not fixed here (needs owners)

The 8 RED gates, the 3 fail-open gates, and the ~20 wrong-reason-class entries
that need a build workflow. Fixing those is unrelated work; getting the
exemptions honest was this lane's deliverable.

## Rule this establishes

A bulk-applied exemption reason is a *hypothesis*, not a fact. The 2026-08-01
seeding assigned 6 reason strings to 347 guards by pattern, and at least 20 of
those assignments were wrong. **Test an exemption by running the thing.** A
reason that names a resource the script never invokes is a false exemption, and
a false exemption is how a RED gate stays invisible.

---

## Follow-up 2026-08-06 (same day): three of this audit's own verdicts were wrong

A follow-up lane took the three worst-class findings above and re-verified each
at `origin/main` before acting. All three re-verifications changed the verdict.
Recording them here because the rule this document establishes — *test an
exemption by running the thing* — applies to this document too.

### 1. The "real proof trust bypass" was a detector false positive

`check-simpleos-critical-formal-proofs.shs` was RED on
`FAIL verification/kernel_capabilities -- contains 1 proof trust bypass(es)
outside comments`. There is **no bypass**. The hit is
`src/verification/kernel_capabilities/KernelCapabilities/SingleUse.lean:3`,
which reads *"a **sorry**-free proof of the"* inside a `/- ... -/` docstring.

Root cause: `scripts/check/check-lean-proofs.shs:36` stripped only `--` LINE
comments (`sed 's/--.*//'`) before the trust grep, so Lean block comments and
docstrings survived it. A prose allowlist (`without sorry` / `no sorry` /
`zero sorry`) covered some phrasings and missed `sorry-free`.

Census across all 38 Lake projects: **21 `TRUST_RE` hits, every one of them
prose inside a `/- -/` docstring**, of which 11 said "sorry-free" and were
therefore unallowlisted. Two projects were falsely red — `kernel_capabilities`
(1 hit) and `os_enforcement` (8).

Fixed in `ecee1902710` by making the header's "excluding comments" contract
true: an awk state machine strips block comments and docstrings with nesting
depth, reset per file so an unterminated comment cannot swallow the next file.
A bypass following a closed block comment on the same line is still counted.
Self-test raised 5 → 7 fixtures. Full run after: `lean-proof-check: PASS — 38
project(s), 99 .lean file(s) checked`.

### 2. The five `*-formal-proofs.shs` "FALSE EXEMPTION, gate is GREEN" verdicts are wrong — the exemptions are GENUINE

The toolchain re-test in the *"Toolchain re-test (the second-pass
correction)"* section above is **invalid for every Lean gate**. It stripped
`~/.elan/bin` from `PATH` — but `check-lean-proofs.shs` never consults `PATH`
first:

```sh
elif [ -x "$HOME/.elan/bin/lake" ]; then
    LAKE="$HOME/.elan/bin/lake"
```

It probes `$HOME/.elan/bin/lake` **directly**. Stripping `PATH` changed
nothing; lake was used throughout. Re-run with `HOME` also neutralised
(`env PATH=/usr/bin:/bin HOME=/nonexistent`), all six Lean gates exit 1 with
`error: lake not found; install via elan or set LAKE_BIN`:
`check-simpleos-{boundary,compiler-language,critical,memory-safety,storage,
ui-policy}-formal-proofs.shs` and `check-cache-identity-formal-proofs.shs`.

They genuinely need the Lean/lake toolchain and are **not** wirable in a
checkout-only job. Their original *hardware* wording was still wrong (no QEMU,
FPGA or board is involved), so the entries were corrected a second time — to a
reason that is true.

This is the same error shape the audit warned about one paragraph earlier, in
the same paragraph that claimed to have controlled for it. A `PATH` strip only
proves independence from `PATH`.

### 3. `check-cuda-generated-2d-readback.shs` is not fail-open

The two digests quoted above differ **by design**. They are provenance hashes
of two distinct artifact FILES, `build/cuda_generated_2d_readback/`
`{expected,actual}-u32.json` — both 1975 bytes and byte-identical except their
`producer` key (`cuda-generated-2d-expected` vs `cuda-generated-2d-readback`).
They are not an expected-vs-actual comparison and comparing them would make the
gate permanently and wrongly red.

The comparison that gates the script is element-wise in the CUDA driver helper:
`expected_checksum=274983770116`, `actual_checksum=274983770116`,
`mismatch_count=0`, over 64 pixels on a real device. Its exit 0 was earned.

What was genuinely missing is what let this be misread: the script ended on a
bare `[ "$(cuda_env_value ..._status)" = "pass" ]`, so its last stdout line was
the unrelated digest pair and it had no verdict and no count. `4917c71d342`
adds one, plus fail-closed branches that did not exist before for
`status=pass` with a nonzero `mismatch_count` and for `status=pass` with a zero
or missing pixel count.

### 4. `qemu-frozen-source-admission.shs` is a library, not a fail-open gate

It lives at `scripts/check/**lib**/` and defines only shell functions
(`qemu_admission_begin` / `_publish` / `_source_snapshot` / `_sha256`), sourced
by QEMU evidence producers. Executing it directly defines functions and
returns; **printing nothing and exiting 0 is correct for a library**.

The real defect is in the enumerator: `check-guard-wiring.shs:79` does
`find "$_root/scripts/check" -type f -name '*.shs'` with no depth limit, so it
sweeps `lib/` into the guard set and five sourced libraries appear as guards
needing an opt-out. Not fixed here: excluding `scripts/check/lib/` would lower
`guard_total` below the published 444 and must land together with removing the
corresponding opt-out entries, or `optout_gone` fires. Filed, not silenced.

Unrelated but noted: this library shells out to `python3`, which violates the
repo's no-Python rule.

### What this follow-up did NOT do

`check-simpleos-critical-formal-proofs.shs` was **not** wired, contrary to the
plan. Its Lean dependency is real (finding 2), and wiring it would put CI red
for a genuine environment reason. Making the exemption *true* is the honest
outcome; making the gate run where it cannot is not.

The other 7 RED gates from the table above are untouched and still need owners.

### Rule this adds

**A capability re-test must remove the capability, not one route to it.** Both
this document's `nvcc` correction and its `PATH`-strip correction were written
to catch exactly this, and the `PATH` strip still missed a hardcoded
`$HOME/.elan/bin` probe. Before claiming a script does not need a tool, grep
the script for every path it could reach that tool by.

---

## Follow-up 2026-08-06 (batch 3): the 127 "not yet triaged" entries, all RUN

The 2026-08-06 audit above examined only the entries that make a *testable
environment claim*. It left **127 entries whose whole stated reason is
"orphaned at the 2026-08-01 wiring audit; not yet triaged"** untouched. Those
are honest-by-construction — they claim nothing — but each is still a
verification gate that NOTHING RUNS, and an unreached check is indistinguishable
from a passing one. This section runs all 127.

### Method

1. **Static resolve** against `check-guard-wiring.shs`'s own enumeration
   (`scripts/check` + `scripts/audit` recursive, plus `scripts -maxdepth 1
   -name 'check-*.shs'`): all 127 basenames resolve to exactly **one** path
   each, none under `scripts/check/lib/`. So **no STALE entry and no
   swept-in-library entry in this set** — those two classes are exhausted by
   the earlier finding.
2. **Hazard screen** before running anything, because two Stage-3 compiles were
   live in this shared working copy. Every `rm -rf` in the set targets a
   script-local `$TMP`/`$BUILD_DIR`. Two scripts spawn a daemon and then
   `pkill` it (`check-wm-daemon-health-recovery-evidence.shs`,
   `check-wm-multiapp-taskbar-evidence.shs`); both are recorded RUN-WITHHELD
   rather than run blind.
3. **Host run:** `setsid timeout -k 5 90 sh <script> </dev/null`, concurrency
   capped, on this plain Linux host. Timeout is recorded **UNKNOWN**, never
   GENUINE.
4. **Clean-checkout re-run**, which is the only test that supports a "wire it"
   verdict. `81338e2ab84` established that stripping `PATH` is not a capability
   test; **stripping `PATH` and `HOME` is not sufficient either** — it still
   runs *in the working tree*, so a gate reading `build/`, `bin/release/` or a
   generated `doc/09_report/` file still sees artifacts a checkout-only runner
   will not have. `soundness-diff.shs` proves it: it reports "PASS — 10
   fixture(s)" under `env -i PATH=/usr/bin:/bin HOME=/nonexistent` with no
   cargo and no compiler on `PATH`, because it finds a prebuilt binary by
   absolute path. Every GREEN verdict below was therefore re-run from a
   pristine `git archive origin/main` tree under `env -i PATH=/usr/bin:/bin
   HOME=/nonexistent`, and only survivors are called GREEN.

   **Rule this adds:** a wirability test must remove the *artifacts* as well as
   the *tools*. Run from a clean checkout, not merely a stripped environment.

### Result

| verdict | n | meaning |
|---|---|---|
| GENUINE | 46 | really needs a built `bin/simple`, a GPU/display, macOS, a board or an emulator |
| RED | 24 | runs here and FAILS, with a real diagnostic, and nothing runs it |
| UNKNOWN | 14 | hit the 90s cap on a load-27 box; NOT claimed genuine |
| GREEN | 14 | passes from a pristine checkout with base tools only — **wirable** |
| FAIL-OPEN | 11 | exits 0 while checking nothing, or while its own output says it failed |
| SILENT-RED | 5 | exits 1 with a **zero-byte** log — no diagnostic at all |
| BROKEN | 4 (+1 stale dep) | script defect, not a real failure |
| NEEDS-DRIVER | 3 | requires `--case`/argv; bare invocation is a usage error |
| SHARED-WC | 2 | failed only on `.git/index` lock contention in this shared copy |
| RUN-WITHHELD | 2 | daemon-spawn + `pkill`, withheld in a shared WC |
| NOT A GATE | 1 | `freeze-tool-qual-golden.shs` is a golden-*freezer* tool |

**46 GENUINE is the honest majority — the 2026-08-01 seeding was right about
most of this set.** But 24 RED + 11 FAIL-OPEN + 5 SILENT-RED = **40 entries
(31%) are gates that are not merely unwired but actively broken or vacuous**,
and nothing has been reporting it.

### The worst findings

- **`check-web-wm-modern-shell-evidence.shs` — FAIL-OPEN, exits 0 with three
  `Segmentation fault` lines in its own output.** Nothing about this run
  succeeded and the gate reports success.
- **`check-portable-compute-toolchains.shs` — exits 0 printing
  `all_portable_compute_candidates_validated=false`,
  `all_portable_compute_pins_verified=false`,
  `all_portable_compute_toolchains_verified=false`.** Its own verdict fields
  say it did not verify, and its exit code says it did.
- **`check-scilib-accelerator-gates.shs` — exits 0 on
  `pytorch_error=libtorch_not_found`.** Absence of the thing under test is
  treated as a pass.
- **`check-llm-runtime-slang-native-capability-probe.shs` — exits 0 with
  `STATUS: PASS ... reason=native_runtime_capabilities_not_linked`.** Same
  shape: the capability is missing, so the probe passes.
- **`check-nvme-firmware-remaining-gates.shs`** exits 0 on `STATUS: POSTPONED
  ... environment-unavailable`, **`check-tauri-ios-mobile-{mdi,renderer}-evidence.shs`**
  exit 0 on `status=unavailable`, **`check-qt-gui-size-baseline.shs`** on
  `comparison_status=unavailable`, **`check-runtime-https-provider.shs`** on
  `STATUS: SKIP SIMPLE_RUNTIME_WM_PATH is not set`. A missing precondition
  should be `ERROR — nothing was checked` (exit 2), not a pass.
- **`check-expect-footgun.shs` prints its violations and exits 0 anyway** — it
  only exits 1 under an off-by-default `STRICT=1`. Wiring it as-is would gate
  nothing. (Not fixed here: flipping the default is an underlying-failure fix,
  out of this lane's scope.)
- **SILENT-RED (5): exit 1, zero bytes of output.** No owner can act on these.
  `check-gui-color-image-pipeline-8k-evidence.shs`,
  `check-gui-wasm-host-wm-launch-evidence.shs`,
  `check-gui-wasm-target-package-evidence.shs`,
  `check-native-capturing-lambda-values.shs`,
  `check-native-concat-string-array-forward.shs`.
- **BROKEN (script defects, not findings):**
  `check-gtk-gui-size-speed-baseline.shs` dies at line 1034 with
  `simple_max_rss_kb: parameter not set`;
  `check-processing-ir-offload-fill-u32-break-even.shs` dies at line 7 with its
  own usage string; `check-responsive-showcase-evidence.shs` and
  `check-wm-daemon-autoconnect-overhead-evidence.shs` core-dump the thing they
  measure (`Segmentation fault` / `Illegal instruction (core dumped)`).
- **`check-scilib-runtime-shims.shs` — exit 127, `src/runtime/scilib/verify_symbols.sh:
  not found`.** The *entry* is not stale but its *dependency* is: the helper it
  execs does not exist in the tree. This qualifies the earlier "no STALE
  entries" claim.
- **RED with real content, nothing running it:** `cert-gate.shs`
  (`CERT-GATE: FAIL (1 phase(s) failed)`), `stress-suite.shs`
  (`RESULT pass=13 fail=4`), `run-tool-qual-corpus.shs`
  (`25 case(s), 23 pass, 2 defect(s)`), `check-vhdl-gen-probes.shs` (5 pass /
  3 fail), `check-vhdl-golden-match.shs` (4 fail),
  `scripts/audit/direct-env-runtime-guard.shs` (a pure grep guard, RED on real
  `rt_env_get` call sites), `check-wc-rollback.shs` (`FOUND 2 file(s)`).

### Not fixed here

Every RED, SILENT-RED, BROKEN and FAIL-OPEN above needs an owner. This lane's
deliverable is making the exemptions HONEST, and per the audit charter the
underlying failures are filed, not fixed — fixing them is unbounded work. No
gate was weakened, skipped or disabled, and no entry was relabelled to make
anything green.

### Full 127-entry classification

`host rc` = exit code on this Linux host (`124`/`137` = 90s cap → UNKNOWN).
`clean-checkout rc` = re-run from a pristine `git archive origin/main` tree
under `env -i PATH=/usr/bin:/bin HOME=/nonexistent`; `n/a` = not a GREEN
candidate, so not re-run.

| gate | verdict | host rc | clean-checkout rc | evidence (last output lines) |
|---|---|---|---|---|
| `check-gtk-gui-size-speed-baseline.shs` | BROKEN | 2 | n/a | scripts/check/check-gtk-gui-size-speed-baseline.shs: 1034: simple_max_rss_kb: parameter not set  |
| `check-processing-ir-offload-fill-u32-break-even.shs` | BROKEN | 2 | n/a | scripts/check/check-processing-ir-offload-fill-u32-break-even.shs: 7: 1: usage: scripts/check/check- |
| `check-responsive-showcase-evidence.shs` | BROKEN | 1 | n/a | timeout: the monitored command dumped core Segmentation fault  |
| `check-wm-daemon-autoconnect-overhead-evidence.shs` | BROKEN | 1 | n/a | Illegal instruction (core dumped) FAIL: no-measurement-produced (see build/wm_daemon_overhead/stderr |
| `check-scilib-runtime-shims.shs` | BROKEN-STALE | 127 | n/a | scripts/check/check-scilib-runtime-shims.shs: 45: src/runtime/scilib/verify_symbols.sh: not found  |
| `check-expect-footgun.shs` | FAIL-OPEN | 0 | 0 | test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:723: expect(compiler == base).to_ |
| `check-llm-runtime-slang-native-capability-probe.shs` | FAIL-OPEN | 0 | n/a | STATUS: PASS llm-runtime-slang-native-capability-probe reason=native_runtime_capabilities_not_linked |
| `check-llm-strict-host-prereq-doctor.shs` | FAIL-OPEN | 0 | 0 | STATUS: WARN llm-strict-host-prereq-doctor blocked_gate_count=4 blocked_gates=dashboard_live_http vl |
| `check-nvme-firmware-remaining-gates.shs` | FAIL-OPEN | 0 | n/a | STATUS: POSTPONED uno-q-supplementary environment-unavailable STATUS: POSTPONED cosmos-board BT-001. |
| `check-portable-compute-toolchains.shs` | FAIL-OPEN | 0 | n/a | all_portable_compute_pins_verified=false all_portable_compute_toolchains_verified=false  |
| `check-qt-gui-size-baseline.shs` | FAIL-OPEN | 0 | 0 | simple_bytes=14336 comparison_status=unavailable  |
| `check-runtime-https-provider.shs` | FAIL-OPEN | 0 | 0 | STATUS: SKIP SIMPLE_RUNTIME_WM_PATH is not set  |
| `check-scilib-accelerator-gates.shs` | FAIL-OPEN | 0 | 0 | pytorch_error=libtorch_not_found pytorch_cuda_available=false  |
| `check-tauri-ios-mobile-mdi-evidence.shs` | FAIL-OPEN | 0 | n/a | ios_reason=iOS simulator evidence requires macOS with Xcode; current host Linux status=unavailable  |
| `check-tauri-ios-mobile-renderer-evidence.shs` | FAIL-OPEN | 0 | n/a | ios_mdi_css_animation_probe= status=unavailable  |
| `check-web-wm-modern-shell-evidence.shs` | FAIL-OPEN | 0 | n/a | Segmentation fault Segmentation fault  |
| `check-aetheric-host-web-gui-evidence.shs` | GENUINE | 1 | n/a | aetheric_host_web_gui_live_qemu=not-applicable aetheric_host_web_gui_live_execution=pending-or-faile |
| `check-cache-identity-formal-proofs.shs` | GENUINE | 0 | n/a | STATUS: PASS lean-proof-check project — 1 project(s), 3 .lean file(s) checked STATUS: PASS cache-i |
| `check-core-runtime-smoke.shs` | GENUINE | 1 | n/a | expected_compile_contains=42 actual_compile=Compiled /tmp/simple-core-smoke-35xC0U.spl -> /tmp/simpl |
| `check-game2d-breakout.shs` | GENUINE | 0 | n/a | overall=pass evidence_log=build/game2d-breakout/evidence.log  |
| `check-game3d-rollball.shs` | GENUINE | 0 | n/a | overall=pass evidence_log=build/game3d-rollball/evidence.log  |
| `check-gtk-gui-repeat-evidence.shs` | GENUINE | 1 | n/a | gtk_gui_repeat_simple_closure_bytes=missing report_path=build/gtk_gui_repeat_evidence/report.md  |
| `check-hosted-wm-capture-evidence.shs` | GENUINE | 1 | n/a | hosted_wm_capture_simple_bin_source=repo-self-hosted-fallback hosted_wm_capture_simple_bin_status=pa |
| `check-lean-proofs.shs` | GENUINE | 0 | n/a | lean-proof-check: PASS — 38 project(s), 99 .lean file(s) checked  |
| `check-linux-hosted-wm-live-window-evidence.shs` | GENUINE | 1 | n/a | linux_hosted_wm_live_window_framebuffer_ppm=missing linux_hosted_wm_live_window_snapshot=missing  |
| `check-llm-runtime-slang-local-readiness.shs` | GENUINE | 1 | n/a | STATUS: FAIL llm-runtime-slang-local-readiness  |
| `check-llm-runtime-slang-native-streaming-evidence.shs` | GENUINE | 1 | n/a | STATUS: FAIL llm-runtime-slang-native-streaming reason=local_readiness_failed  |
| `check-llm-runtime-vllm-host-env-contract.shs` | GENUINE | 1 | n/a | STATUS: FAIL llm-runtime-vllm-host-env-contract reason=probe_exit_expected_0_got_1  |
| `check-llm-runtime-vllm-host-probe.shs` | GENUINE | 1 | n/a | STATUS: FAIL llm-runtime-vllm-host-probe reason=missing_reason  |
| `check-low-dependency-dynsmf-build-plans.shs` | GENUINE | 1 | n/a | low_dependency_dynsmf_plan_stderr=build/low_dependency_ui_dynsmf/build_plans/plan.err low_dependency |
| `check-make-os-disk-fat32-integrity.shs` | GENUINE | 1 | n/a | missing FAT32 integrity checker dependency: mdir  |
| `check-native-consecutive-zero-arg-receiver.shs` | GENUINE | 2 | n/a | native consecutive zero-arg receiver: missing self-hosted SIMPLE_BIN  |
| `check-native-immutable-fn-receiver.shs` | GENUINE | 2 | n/a | immutable fn receiver closure: missing self-hosted SIMPLE_BIN  |
| `check-native-sspec-expect-helper.shs` | GENUINE | 1 | n/a | Use angle brackets: raw<...> instead of raw[...]  |
| `check-processing-ir-offload-break-even.shs` | GENUINE | 1 | n/a | processing_ir_offload_ptx_artifact_validated=true processing_ir_offload_ptx_source_hash_equal=true  |
| `check-process-parent-death.shs` | GENUINE | 1 | n/a | process_parent_death=false error=SIMPLE_RUNTIME is required  |
| `check-production-gui-font-offload-evidence.shs` | GENUINE | 1 | n/a | production_gui_font_offload_report=doc/09_report/production_gui_font_offload_evidence_2026-08-06.md  |
| `check-production-gui-font-runtime-evidence.shs` | GENUINE | 1 | n/a | production_gui_font_runtime_bitmap_backend_submit_ok=false production_gui_font_runtime_bitmap_readba |
| `check-production-gui-web-backend-executed-evidence.shs` | GENUINE | 1 | n/a | production_gui_backend_simple_bin_status=forbidden report_path=doc/09_report/production_gui_web_back |
| `check-rv32-nvme-nand-recovery.shs` | GENUINE | 0 | n/a | STATUS: PASS rv32-nvme-nand-recovery self-test  |
| `check-seed-native-build-invariant.shs` | GENUINE | 1 | n/a | [gc-warning] Higher-layer module 'std.nogc_sync_mut.daemon_sdk.protocol' (family: nogc_sync_mut) imp |
| `check-tauri-android-mobile-renderer-evidence.shs` | GENUINE | 1 | n/a | status=fail reason=Android APK build failed; see /home/ormastes/dev/pub/simple/build/tauri_android_m |
| `check-tauri-android-webview-proof.shs` | GENUINE | 1 | n/a | status=fail reason=Chrome not found  |
| `check-tauri-mobile-mdi-evidence.shs` | GENUINE | 1 | n/a | tauri_mobile_mdi_simple_bin_source=repo-self-hosted-fallback tauri_mobile_mdi_simple_bin_status=pass |
| `check-tauri-mobile-renderer-parity-evidence.shs` | GENUINE | 1 | n/a | tauri_mobile_renderer_parity_android_logcat= tauri_mobile_renderer_parity_android_gpu_log=  |
| `check-test-runner-outcome-exits.shs` | GENUINE | 1 | n/a | Simple Test Runner child error: expected .spl test file: build/test-runner-outcome-exits.1030068/emp |
| `check-test-runner-rss-batch.shs` | GENUINE | 1 | n/a | error=runner_failed:1  |
| `check-thread-spawn-with-args-native.shs` | GENUINE | 0 | n/a | thread_spawn_with_args_native=true smoke=test/01_unit/lib/nogc_async_mut/thread_spawn_with_args_nati |
| `check-titlebar-cross-engine-parity.shs` | GENUINE | 1 | n/a | status=fail reason=WebKit capture requires macOS (uname=Linux)  |
| `check-ui-cli-live-transport.shs` | GENUINE | 1 | n/a | ui-cli-live-transport: deployed runtime is the Rust bootstrap seed, not Pure Simple  |
| `check-unoq-wm-full-stack.shs` | GENUINE | 1 | n/a | unoq_wm_full_stack_reason=qrb2210-simpleos-port-unavailable unoq_wm_full_stack_stm32_desktop_accepte |
| `check-vector-font-compute-evidence.shs` | GENUINE | 0 | n/a | vector_font_compute_gpu_glyph_returned=true vector_font_compute_production_offload_ready=true  |
| `check-wasm-hello-gui-package-evidence.shs` | GENUINE | 1 | n/a | simple_bin_source=repo-self-hosted-fallback simple_bin_status=pass  |
| `check-web-draw-ir-route-key-sdn-overhead.shs` | GENUINE | 125 | n/a | web_draw_ir_sdn_medium_bytes= web_draw_ir_sdn_large_bytes=  |
| `check-widget-shells-crossengine-evidence.shs` | GENUINE | 1 | n/a | widget_crossengine_status=unavailable widget_crossengine_reason=chrome-binary-unavailable  |
| `check-widget-showcase-4k-200fps.shs` | GENUINE | 1 | n/a | gui_showcase_4k_200fps_time_log=build/widget-showcase-4k-200fps/time.log gui_showcase_4k_200fps_time |
| `check-window-winit-leak.shs` | GENUINE | 2 | n/a | SKIP: no GUI-enabled driver (build: cd src/compiler_rust && CARGO_TARGET_DIR=target/gui cargo build  |
| `check-wm-gui-window-drawing-evidence.shs` | GENUINE | 1 | n/a | wm_gui_window_drawing_status=unavailable wm_gui_window_drawing_reason=missing-command:sips  |
| `fuzz-diff.shs` | GENUINE | 0 | n/a | -- summary: 200 generated, 200 ran, 0 empty/invalid, 0 DIVERGENCE(S) -- RESULT: no divergence over b |
| `sanitizer-matrix.shs` | GENUINE | 0 | n/a | ------------------------------------------------------------- waivers: 0 active, 0 EXPIRED ledger: / |
| `soundness-diff.shs` | GENUINE | 0 | n/a | -- summary: 10 fixture(s), 10 sound+correct, 0 defect(s) -- RESULT: PASS (interpret == compiled == e |
| `tool-qual-meta.shs` | GENUINE | 0 | n/a | -- summary: 18 (case,mode) check(s), 18 deterministic, 0 nondeterminism defect(s) -- RESULT: PASS (e |
| `check-gui-web-2d-completion-criteria-placeholders.shs` | GREEN | 0 | 0 | gui_web_2d_completion_criteria_missing_required_gates= gui_web_2d_completion_criteria_report=doc/09_ |
| `check-gui-web-2d-headless-handoff-negative-selftest.shs` | GREEN | 0 | 0 | gui_web_2d_headless_handoff_negative_selftest_cases=duplicate-gate gate-value host-count runbook-cou |
| `check-gui-web-2d-parallel-agent-review-evidence.shs` | GREEN | 0 | 0 | gui_web_2d_parallel_agent_review_reviewed_findings_status=pass gui_web_2d_parallel_agent_review_repo |
| `check-gui-widget-rendering-fixture-coverage.shs` | GREEN | 0 | 0 | gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_classes=panel:widget-panel,text:widge |
| `check-html-css-rendering-manifest-traceability.shs` | GREEN | 0 | 0 | html_css_rendering_manifest_traceability_fixture_scene_count=55 html_css_rendering_manifest_traceabi |
| `check-llm-feature-db-reference-integrity.shs` | GREEN | 0 | 0 | STATUS: PASS llm-feature-db-reference-integrity rows_checked=11 paths_checked=292 missing_count=0 st |
| `check-llm-finetune-setup-contract.shs` | GREEN | 0 | 0 | STATUS: PASS llm-finetune-setup-contract checked_count=34  |
| `check-llm-runtime-slang-setup-contract.shs` | GREEN | 0 | 0 | STATUS: PASS llm-runtime-slang-setup-contract checked_count=41  |
| `check-llm-runtime-torch-setup-contract.shs` | GREEN | 0 | 0 | STATUS: PASS llm-runtime-torch-setup-contract checked_count=33  |
| `check-llm-strict-host-prereq-doctor-contract.shs` | GREEN | 0 | 0 | STATUS: PASS llm-strict-host-prereq-doctor-contract checked_count=10  |
| `check-llm-tooling-public-absence-rendering.shs` | GREEN | 0 | 0 | STATUS: PASS llm-tooling-public-absence-rendering  |
| `check-process-parent-death-c.shs` | GREEN | 0 | 0 | process_parent_death_c=true  |
| `check-runtime-https-openssl.shs` | GREEN | 0 | 0 | SELFCHECK PASSED mode=trickle STATUS: PASS runtime HTTPS OpenSSL  |
| `codex-run-guard-test.shs` | GREEN | 0 | 0 | [codex-run-guard] guard active (bypass=0 max_seconds=1 max_rss_mb=0 max_session_tokens=0) -> /tmp/tm |
| `check-llm-caret-installed-claude-cli.shs` | NEEDS-DRIVER | 2 | n/a | usage: sh scripts/check/check-llm-caret-installed-claude-cli.shs --case <prerequisites version help  |
| `check-llm-caret-tui-pty.shs` | NEEDS-DRIVER | 2 | n/a | usage: sh scripts/check/check-llm-caret-tui-pty.shs --case <prerequisites routing lifecycle editing  |
| `codex-run-guard.shs` | NEEDS-DRIVER | 1 | n/a | Error: stdin is not a terminal  |
| `freeze-tool-qual-golden.shs` | NOT-A-GATE | 0 | n/a | # Env knobs: # SIMPLE_BIN compiler binary, used only to print the observed output for  |
| `cert-gate.shs` | RED | 1 | n/a | totals: 1 FAIL, 1 WARN CERT-GATE: FAIL (1 phase(s) failed)  |
| `check-famous-site-corpus-div-geometry-chunks.shs` | RED | 1 | n/a | report_path=doc/09_report/famous_site_corpus_div_geometry_chunks_2026-08-06.md blur_or_tolerance_use |
| `check-gui-wasm-cli-artifact.shs` | RED | 1 | n/a | gui_wasm_cli_builder_matrix_import_count=0 gui_wasm_cli_builder_matrix_imports=  |
| `check-gui-web-2d-platform-evidence-bundle.shs` | RED | 1 | n/a | gui_web_2d_platform_evidence_bundle_windows_vulkan_env=build/gui_renderdoc_feature_coverage_status/e |
| `check-gui-web-2d-platform-freshness.shs` | RED | 1 | n/a | gui_web_2d_platform_freshness_production_env=build/production_gui_web_renderer_parity_evidence/evide |
| `check-html-css-full-rendering-goal-status.shs` | RED | 1 | n/a | html_css_full_rendering_goal_manifest_case_count=50 html_css_full_rendering_goal_manifest_required_c |
| `check-html-css-sspec-traceability.shs` | RED | 1 | n/a | html_css_sspec_traceability_manual_count= html_css_sspec_traceability_receipt_sha256=  |
| `check-llm-caret-claude-cli-trace.shs` | RED | 1 | n/a | llm_caret_symbol_traced_count=506 STATUS: FAIL llm-caret-claude-cli-trace  |
| `check-llm-caret-full-parity-implementation.shs` | RED | 1 | n/a | class_target_files_missing=15 STATUS: FAIL llm-caret-full-parity-implementation  |
| `check-llm-caret-full-parity-plan.shs` | RED | 1 | n/a | full_parity_symbol_rows=14119 STATUS: FAIL llm-caret-full-parity-plan  |
| `check-llm-finetune-acceptance-evidence.shs` | RED | 1 | n/a | STATUS: FAIL llm-finetune-acceptance reason=BLOCKED_RETRY6_NOT_READY  |
| `check-llm-finetune-guard-evidence.shs` | RED | 1 | n/a | STATUS: FAIL llm-finetune-guard-evidence  |
| `check-llm-strict-blocker-tracker.shs` | RED | 1 | n/a | STATUS: FAIL llm-strict-blocker-tracker reason=default_missing_vllm_count default_missing_vllm_sha25 |
| `check-llm-tooling-context-ponytail-full-replacement.shs` | RED | 1 | n/a | STATUS: FAIL llm-tooling-context-ponytail-full-replacement failures=mimic_evidence,execution_spec,ex |
| `check-llm-tooling-context-ponytail-mimic.shs` | RED | 1 | n/a | STATUS: FAIL llm-tooling-context-ponytail-mimic  |
| `check-mcp-lsp-nfr-evidence.shs` | RED | 1 | n/a | error=lsp_request_timeout:lsp-request-9  |
| `check-rv32-nvme-host-axi-mmio.shs` | RED | 1 | n/a | FAIL: endpoint missing x"00001000"  |
| `check-shared-wm-renderer-unification-evidence.shs` | RED | 1 | n/a | shared_wm_renderer_unification_check_log=build/shared_wm_renderer_unification_evidence/check.out sha |
| `check-vhdl-gen-probes.shs` | RED | 1 | n/a | vhdl_gen_probes_fail=3 vhdl_gen_probes_ok=false  |
| `check-vhdl-golden-match.shs` | RED | 1 | n/a | vhdl_golden_match_rest_missing=0 vhdl_golden_match_ok=false  |
| `check-wc-rollback.shs` | RED | 1 | n/a | check-wc-rollback: FOUND 2 file(s) rewound to an older ancestor version (not origin/main, not HEAD)  |
| `direct-env-runtime-guard.shs` | RED | 1 | n/a | src/app/web_dashboard/server.spl:38: rt_env_get("DASH_AUTH") == "1" STATUS: FAIL direct env/process  |
| `run-tool-qual-corpus.shs` | RED | 1 | n/a | -- summary: 25 case(s), 23 pass, 2 defect(s) -- RESULT: FAIL (tool-qualification corpus found 2 defe |
| `stress-suite.shs` | RED | 1 | n/a | RESULT pass=13 fail=4 STRESS GATE: FAIL  |
| `check-wm-daemon-health-recovery-evidence.shs` | RUN-WITHHELD | WITHHELD | n/a | (no output at all) |
| `check-wm-multiapp-taskbar-evidence.shs` | RUN-WITHHELD | WITHHELD | n/a | (no output at all) |
| `check-rendering-source-coupling.shs` | SHARED-WC | 1 | n/a | 1: Could not acquire lock for index file 2: The lock for resource '/home/ormastes/dev/pub/simple/.gi |
| `check-ui-cli-final-review.shs` | SHARED-WC | 1 | n/a | 2: The lock for resource '/home/ormastes/dev/pub/simple/.git/index' could not be obtained immediatel |
| `check-gui-color-image-pipeline-8k-evidence.shs` | SILENT-RED | 1 | n/a | (no output at all) |
| `check-gui-wasm-host-wm-launch-evidence.shs` | SILENT-RED | 1 | n/a | (no output at all) |
| `check-gui-wasm-target-package-evidence.shs` | SILENT-RED | 1 | n/a | (no output at all) |
| `check-native-capturing-lambda-values.shs` | SILENT-RED | 1 | n/a | (no output at all) |
| `check-native-concat-string-array-forward.shs` | SILENT-RED | 1 | n/a | (no output at all) |
| `check-async-library-hardening-evidence.shs` | UNKNOWN | 124 | n/a | async_library_hardening_spec=test/01_unit/lib/async/async_basics_spec.spl status=pass passed=25 fail |
| `check-gui-low-res-readability.shs` | UNKNOWN | 124 | n/a | Testing resolution: 800x600  |
| `check-gui-web-2d-headless-handoff-prep.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-link-native-build-parity.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-llm-goal-evidence.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-nvme-rv32-minimal-live.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-office-desktop-render.shs` | UNKNOWN | 124 | n/a | Pulling lscr.io/linuxserver/libreoffice:latest ...  |
| `check-processing-fill-wire-copy.shs` | UNKNOWN | 124 | n/a | [STDERR] error: native-build worker exited with code 1. [STDERR] interpreter: /home/ormastes/dev/pub |
| `check-ui-native-size-audit.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-vector-font-compute-matrix-evidence.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `check-wm-launch-capture-evidence.shs` | UNKNOWN | 124 | n/a | > SIMPLE_ELECTRON_PROOF_PATH=${SIMPLE_ELECTRON_PROOF_PATH:-../../build/electron_shell_envelope.json} |
| `check-wm-production-fullscreen-evidence.shs` | UNKNOWN | 124 | n/a | (no output at all) |
| `redeploy_gate.shs` | UNKNOWN | 124 | n/a | SKIP cfg-lowered-funcs=2 fixture runs; count-check needs --emit/dump flag (ponytail) --------------- |
| `sync-native-health-guard.shs` | UNKNOWN | 137 | n/a | sync-native-health-guard: running smoke test (native-build)... Killed  |

### Correction to the batch-3 wiring commit (895caa46b2a)

That commit's closing paragraph says "The RED, SILENT-RED, BROKEN and FAIL-OPEN
gates found in the batch-3 triage stay exempt." **That is false about four of
its own 17 removals**, and it is the same defect shape `81338e2ab84` had to
correct one level up. Recorded here rather than left standing:

| removed exemption | batch-3 verdict |
|---|---|
| `check-llm-finetune-acceptance-evidence.shs` | **RED** (`STATUS: FAIL llm-finetune-acceptance reason=BLOCKED_RETRY6_NOT_READY`) |
| `check-llm-finetune-guard-evidence.shs` | **RED** (`STATUS: FAIL llm-finetune-guard-evidence`) |
| `check-llm-runtime-slang-native-capability-probe.shs` | **FAIL-OPEN** (exit 0, `reason=native_runtime_capabilities_not_linked`) |
| `check-llm-strict-host-prereq-doctor.shs` | **FAIL-OPEN** (exit 0, `STATUS: WARN blocked_gate_count=5`) |

The **removals stand** — each is genuinely executed as a subprocess by a wired
contract gate, verified at the `sh scripts/check/<name>.shs` call site — but
"they stay exempt" was wrong and two FAIL-OPEN gates are now inside a wired
pipeline.

**What the four wired contract gates actually assert.** Only
`check-llm-strict-host-prereq-doctor-contract.shs` asserts its subject's exit
code (`doctor_exit != 0` → `add_failure`). The other three
(`slang`/`torch`/`finetune`) *record* `native_exit` / `local_exit` /
`probe_exit` / `acceptance_exit` / `guard_exit` into their evidence env and
never assert them. Their 41 / 33 / 34 cases are `require_env_key` and
`require_report_key` assertions: each requires a named key to be present with a
non-empty value in the subject's emitted env file or report. So the counts are
**real and non-vacuous — they are evidence-shape assertions — but they are not
success assertions**. `check-llm-runtime-slang-local-readiness.shs` exits 1
standalone while its parent contract exits 0.

That is not a reason to unwire them and it is not fixed here (changing an
expectation is an underlying-failure fix, out of this lane's scope). It is
recorded so the next lane does not re-litigate it: **a contract gate that
validates the shape of its subject's failure needs an owner to decide whether
the subject's success should also be asserted.** Compare
`check-llm-runtime-vllm-host-env-contract.shs`, which *does* assert exit 0 and
is correspondingly RED with `reason=probe_exit_expected_0_got_1`.

One further note for whoever owns the CI job: `require_report_key` uses `rg`
(ripgrep). If a runner lacks it the gate fails loudly (`rg` exits 127, the
negated test adds a failure) rather than silently passing, so this is a visible
red, not a new fail-open.

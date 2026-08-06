# guard_wiring_optout.txt carries a family of FALSE exemptions, several hiding RED gates

- **Date:** 2026-08-06
- **Status:** OPEN (exemption reasons corrected; the RED gates behind them need owners)
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

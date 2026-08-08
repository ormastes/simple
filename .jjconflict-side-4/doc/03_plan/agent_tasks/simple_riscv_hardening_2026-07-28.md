# Simple RISC-V Hardening — Detailed Parallel-Agent Plan (2026-07-28)

Supersedes the baseline in `simple_riscv_hardening_2026-07-27.md` §1. That plan's
lane structure and its retractions (§1.1b–§1.1e) remain valid and are NOT repeated
here — read them before starting. This document replaces only the *measured state*
and the *work assignment*.

SPipe state: `.spipe/simple_riscv_hardening/state.md` (phase 5-implement)
Roadmap: `doc/03_plan/hardware/riscv/riscv_gen2_production_roadmap_2026-07-27.md`

---

## 1. Measured baseline — 2026-07-28, every row from a run, not a read

Six gates launched in parallel against `origin/main`. Raw logs:
`~/.claude/jobs/4403a7d8/tmp/rv/*.log`.

| Gate | Exit | Result |
|---|---|---|
| `check-riscv-rtl-truth.shs` | **0** | `riscv_rtl_truth_ok=true` — no fake-CPU evidence |
| `check-riscv-hardware-gates.shs` | 1 | **21/22 PASS** — sole failure `addr4g_probe` (2 sub-checks) |
| `check-riscv-product-level-evidence.shs` | 1 | **its own 9 specs pass 9/9**; fails only on an inherited self-test |
| `check-riscv-fpga-sidecar-contract.shs` | 1 | *"must use self-hosted Simple, not Rust seed"* |
| `check-riscv-formal-dual-track.shs` | 1 | blocked on the sidecar self-test above |
| `check-riscv-budget-evidence.shs` | 1 | generated default BYL ≠ `src/verification/riscv_product/riscv_product.byl` |

### 1.1 Three of the five failures are ONE root cause — and it is not a RISC-V bug

`fpga-sidecar-contract`, `formal-dual-track`, and `product-level-evidence` all fail
for the same reason: **there is no deployed pure-Simple binary**, so the
seed-identity guard (`scripts/check/lib/require-self-hosted.shs`, landed
`c5d5344c2ef6`) refuses to certify evidence produced by the Rust seed.

**This is the guard working.** Before that landed, these gates resolved
`${SIMPLE_BIN:-bin/simple}`, got the seed, and reported PASS — 92 scripts claimed
self-hosted and only 9 verified it. Today's red is *more* truthful than
yesterday's green. Do not "fix" it by relaxing the guard; that would restore a
fail-open gate. See `doc/08_tracking/todo/check_scripts_seed_identity_fail_open_2026-07-28.md`.

**Consequence for planning:** RISC-V hardening is now gated on the self-hosted
deploy, which is gated on stage-4, which is gated on the HIR facade sweep
(`resolve_package_sibling_symbols`, 99.96% of `tokens` lowering time — see
`doc/08_tracking/bug/hir_lowering_quadratic_symbol_define_2026-07-28.md`).
**Lanes R1–R3 below are the only RISC-V work that can finish without that deploy.**
Everything else is correctly blocked and must be reported as blocked, never as
scoped-out or skipped.

### 1.2 The genuinely independent RISC-V defects

Only two. Both are real, both are actionable today.

**`addr4g_probe` — 2 failures** (`build/riscv_hw_gates/addr4g_probe.log`):
```
FAIL rv64 DTB overlay magic byte @0x88000000 == 0xD0
FAIL rv64 DTB overlay is read-only (write ignored, still 0xD0)
```
Above-4 GiB addressing on rv64. The overlay is either not placed, placed at the
wrong physical address, or not write-protected. Note the second check depends on
the first — if the byte is never 0xD0, the read-only assertion is vacuous, so
**fixing #1 may unmask a real #2 rather than fix both.**

**BYL divergence:** the generated default BYL no longer matches the checked-in
`riscv_product.byl`. Per the SPipe rule, BYL is a backend/interchange surface and
**not** the proof result: added proof intent belongs in the manual Lean theorem or
constraint file, and the generated contract must name any BYL export the manual
layer consumes. So the question is not "regenerate to match" — it is **which side
is right**, and whether a manual proof depends on the diverged export.

---

## 1.3 RESULTS — R1, R2, R3 complete (2026-07-28, same day)

Re-run and independently confirmed by the coordinator on `origin/main`:

| Gate | Was | Now |
|---|---|---|
| `check-riscv-hardware-gates.shs` | 1, 21/22 | **0, 22/22 PASS** |
| `check-riscv-budget-evidence.shs` | 1 | **0** (`WARN target-metadata-only` = normal no-Vivado path) |

**R1 — `addr4g_probe`: the probe's setup was stale, not rv64 addressing.**
`soc64_dtb_read` fetches the FDT from DRAM at +128 MiB, but the probe built a
**4 MiB** SoC that has neither the window nor the blob, so the read was simply
out-of-DRAM → 0. Git-proven: at the probe's authoring commit the DTB came from a
*pure function*, so the 4 MiB SoC was legitimate then; the DTB later became a
RAM-backed overlay and the probe was never updated. Overlay *semantics* were
always correct. Fixed by running the overlay checks against the production path,
plus a non-vacuity guard asserting the DTB window lies inside DRAM — without it
the store is dropped as unmapped and read-only passes without exercising the guard.

**§1.2's "the two sub-checks may be dependent" suspicion is REFUTED**, independently,
by R3: with the write-guard removed and the DTB present, magic-byte passes while
read-only fails **alone**. The relation is *subsumption* (same read, same expected
value), not vacuity — it never passes spuriously. The plan's `rc=2` was the probe's
failure *count*, and the "ALL PASS" in its log was a shared-log-path race.

**R2 — the checked-in BYL was asserting things that were false.**
Four facts diverged. The generator is authoritative: `XLen.linux_abi()` returns
soft-float because the cores have no F/D unit, and its sibling validator *actively
rejects* `ilp32d`/`lp64d` — the checked-in file asserted an ABI the generator
refuses to emit. Worse, `formal_gate = "rvfi+sby"` claimed a formal pass that never
ran, while the generated VHDL is a placeholder emitting
`GENERATED_RTL_NOT_IMPLEMENTED` — the exact fabricated-evidence class
`check-riscv-rtl-truth.shs` exists to catch.

The manual proof layer **did** depend on it: `Constraints.lean` asserted
`Abi.ilp32d`/`lp64d` and `FormalGate.rvfiSby`, and `Generated.lean` could not even
*express* the honest values. Regenerating only the BYL would have left the proof
layer certifying hard-float and a passing formal gate while the interchange surface
said the opposite. Both were updated together; intent was preserved rather than
dropped (`formal_flow` still names the designated track), and three new theorems
were added so the honest state is *enforced*, not merely recorded. Proved the proof
gates by injection: re-introducing either false claim breaks `lake build`.

**Two gates were mutually unsatisfiable.** `check-riscv-formal-dual-track.shs:102`
and `check-simpleos-byl-sby-artifacts.shs:56` *required* `formal_gate = "rvfi+sby"`
in the same file `check-riscv-budget-evidence.shs` required to equal a generator
output containing `placeholder-rejected`. **No possible file satisfied both.** It
went unnoticed because both claimants also fail earlier on the R4-blocked seed
identity self-test.

**R3 — all 22 gates injected with the defect each claims to catch. No fail-open
gate found**; 21 gate correctly and name the injected defect. Three findings filed:
`ghdl_validate_rv32` runs `--analyze` only, so it proves the VHDL *parses* and
nothing more (every historical fake-CPU artifact would pass it, yet it counts
toward a hardware claim); the jtag STAGE1 IDCODE check is **self-referential** (the
testbench feeds the DUT its own `EXPECTED_IDCODE` via generic map, so a wrong
IDCODE cannot fail it); and the runner shares a log path across probes, which
raced. Two FPU probes initially *looked* fail-open — that was an out-of-coverage
mutation, not a gate defect, caught by re-injecting in scope. Worth repeating: a
gate that survives one injection is not proven; the mutation must be in scope.

### Still open

- **R4 (HIR facade sweep) — critical path.** Three gates remain blocked on the
  self-hosted deploy, exactly as §1.1 predicted.
- ~~`check-riscv-fpga-sidecar-contract.shs` stale expectations~~ **FIXED
  `f3c351ff0bc`**: five stale asserts replaced with the generator's honest
  values (cross-checked against `riscv_fpga_linux.spl:890-906` AND a real
  generated bundle), each paired with a `check_absent` of the old claim so BOTH
  a stale-old-claim and a fabricated `rvfi-ready`/PASS fail. Injection-proven
  both directions under a self-hosted shim (stale → exit 1 naming the mismatch;
  honest → `STATUS: PASS`). The seed-identity guard is untouched and still
  fires first — the full gate stays red until the deploy, correctly. Its
  `--self-test` also fails closed pre-deploy (pre-existing, reproduced at HEAD):
  the deployed `bin/release/simple` wrapper refuses as "non-production runtime",
  so the not-a-seed probe cannot pass until a production self-hosted binary
  exists. That belongs to the deploy, not this script.
- Pre-existing, unrelated: `soc_top_64` fails `bin/simple compile`
  (`undefined identifier: lsu64_load`, present at HEAD, de-JITs
  `core64_combinational` to the interpreter on every run);
  `soc_top_64_protected_spec.spl` fails with `parse: expected Let, found Dot`;
  `riscv_fpga_linux.spl` fails with `undefined identifier: CORE32_S_INTERRUPT_MASK`.

## 2. Standing rules for every lane

Inherited from the 2026-07-27 plan §2, plus these, all learned the hard way today:

1. **`bin/simple lint` is not a gate.** It exits 0 on files that do not parse. Use
   `bin/simple compile <file>`.
2. **Engine selection:** `SIMPLE_NO_JIT=1` does nothing. Use
   `SIMPLE_EXECUTION_MODE=interpret`; an unrecognized value silently runs the JIT.
   Guide: `doc/07_guide/runtime/execution_engine_selection.md`.
3. **Runs die at ~60 s** unless you raise `SIMPLE_TIMEOUT_SECONDS`
   (`scripts/resource/kill_simple_monitor.shs`). A killed run presents as
   `no examples executed` / FAIL, not as a timeout.
4. **`.get()` is unsafe.** `list.get(i)` returned `value<<3` until today;
   `Dict.get(k)` on a miss returns the value type's **zero, not nil**, so
   `?? default` never fires and `== nil` is false. Use `contains_key` + `d[k]`,
   and `xs[i]` for lists.
5. **Verify KAT constants against an independent implementation** before believing
   a crypto/formal failure. A fabricated BIP-39 vector failed correct code today.
6. **Shared working copy.** Never `git add -A` / `jj commit -a`. Re-fetch *and*
   re-hash the blob immediately before every push — a fresh BASE with a stale blob
   deleted 117 lines of another session's work today. **Abort any push whose
   diffstat is deletions-only when you meant to add.**
7. **Board-runnable rule** (`.claude/rules/board-runnable.md`): a QEMU-only result
   is a defect, not a completion, unless the user scoped it to QEMU. Real-firmware
   proxy always — OpenSBI/OVMF/EDK2, never `-kernel`, never `isa-debug-exit`.
8. **Report blocked as blocked.** A lane that cannot finish keeps its acceptance
   IDs, keeps its TODO open, and blocks the phase. Postponement is not completion.

---

## 3. Lane assignments — parallel, independent, no shared files

| Lane | Scope | Blocked by deploy? | Files |
|---|---|---|---|
| **R1** | `addr4g_probe` rv64 above-4GiB DTB overlay: place, verify, write-protect | No | rv64 DTB/overlay setup + probe |
| **R2** | BYL divergence: decide which side is authoritative, reconcile, prove the manual proof layer still gates | No | `src/verification/riscv_product/**` |
| **R3** | Gate-honesty audit: prove each of the 22 hardware gates FAILS when it should | No | `scripts/check/**` (read-mostly) |
| **R4** | Unblock the deploy: HIR facade sweep — the real gating item | — | `src/compiler/20.hir/**` |

R1–R3 run now, in parallel, and can complete. R4 is the critical path for
everything else and is the only lane whose completion unblocks R5+.

### Lane R3 rationale — why a gate audit is RISC-V work

`check-riscv-rtl-truth.shs` exists precisely because fake-CPU evidence (empty
architecture, a `smoke_handoff` step-counter core, a decode-free core, a wrapper
instantiating an undefined entity) has shipped before. Today's repo-wide finding is
that ~70 of 92 check scripts were fail-open. **A green RISC-V gate is not evidence
until that gate has been seen to fail.** R3 injects each defect a gate claims to
catch and confirms non-zero exit. Any gate that cannot be made to fail is itself a
finding.

---

## 4. Exit criteria

- R1: `check-riscv-hardware-gates.shs` → **22/22**, exit 0, with the read-only
  assertion proven non-vacuous (show it failing when write-protection is removed).
- R2: `check-riscv-budget-evidence.shs` exit 0, **and** the manual proof entry
  point named and re-run (`lake build` / `simple verify check`), not just the
  generated contract.
- R3: every hardware gate demonstrated failing on an injected defect; fail-open
  gates filed.
- R4: stage-4 completes; self-hosted binary deployed; then re-run all six gates —
  the three seed-blocked ones must go green *on their own evidence*.

**Whole-lane exit:** all six gates exit 0 against a deployed pure-Simple binary,
with board-runnable evidence per `.claude/rules/board-runnable.md` for any
hardware claim. Until R4 lands, the honest status is
**"3 gates blocked on self-hosted deploy; 2 real defects open; 1 green."**

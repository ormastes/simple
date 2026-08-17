# QEMU SIMD and coverage gate lane system-test plan

Status: Modern step-based SSpec source and authored mirror complete; native
execution, pure-Simple doc generation, and maintenance are TEST_BLOCKED — no
admitted pure-Simple CLI exists in this environment.

## Scope

This focused system test covers the static-prerequisite tier of the QEMU SIMD
lane and the binary-independent half of the SIMD coverage lane: the
baremetal object gate (`check-simpleos-qemu-engine2d-simd-kernels.shs`), its
instruction-assertion spelling, its non-vacuity against real disassembly, and
the two coverage gates that need no deployed compiler
(`check-engine2d-simd-c-kernels.shs`, `check-x25519mlkem768-cpu-simd.shs`)
plus the 8K operation receipt's honesty flag.

It excludes, deliberately: QEMU guest hit/chunk receipts, QMP frame captures,
the arch-matrix gate and `check-render2d-coverage.shs` (both require a
deployed `bin/simple`), and every RenderDoc/Electron/Chrome comparison lane.
Those remain mandatory before a SimpleOS backend may be marked verified; this
spec does not stand in for them.

Executable:
`test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl`.

Authored mirror:
`doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md`.

## Why this lane needed a spec at all

On 2026-08-16 the object gate was found exiting **1 with zero lines of
output**. Its ARM64 NEON store assertion used a doubled-backslash ERE, which
matches a literal backslash; llvm-objdump emits `st1` + tab + `{ v0.4s },
[x0]`, with no backslash. Under `set -eu` the unmatched `grep -Eq` aborted the
script before its three remaining assertions ever ran. The gate had never
passed. Nothing in the repo noticed, because a caller reading a pipeline's
status sees `tail`'s 0, not the script's 1.

Repaired at commit `25dc443e44a`. This spec exists so the repair cannot
silently regress and so the failure mode itself — a status with no text behind
it — is an assertable property.

## Frozen primary flow

1. `Require the disassembly toolchain — absence of a tool is not a pass`
2. `Run the QEMU SIMD object gate`
3. `Reject a silent verdict: the 2026-08-16 failure printed nothing at all`
4. `Prove the correct pattern matches while the over-escaped one matches nothing`
5. `Pin the coverage gates' stated verdicts, not just their exit status`

## Traceability matrix

| Requirement | Test cases | Observable oracle | Coverage |
|---|---:|---|---|
| REQ-QEMU-SIMD-COV-LANE-001 | primary | gate exit 0 AND stdout length > 0 AND exact PASS line | Full for the static tier |
| REQ-QEMU-SIMD-COV-LANE-002 | spelling | source contains single-escaped `st1` form, does not contain doubled form | Full |
| REQ-QEMU-SIMD-COV-LANE-003 | spelling | all four of `dup`/`st1`/`pshufd`/`movdqu` present | Full |
| REQ-QEMU-SIMD-COV-LANE-004 | non-vacuity | `grep -Eq` exits 0 on correct pattern, **1** on historical pattern | Full negative control |
| REQ-QEMU-SIMD-COV-LANE-005 | coverage | `engine2d-simd-c-kernels: pass`, `STATUS: PASS` on stdout | Partial: two binary-independent gates only |
| REQ-QEMU-SIMD-COV-LANE-006 | coverage | receipt pins `..._80fps_proven=false`, never `=true` | Full for the honesty flag |

## Fail-closed policy

There is no skip path. `clang --version` and `llvm-objdump --version` are
asserted to exit 0; an unqualified host FAILS rather than reporting a green
run over an empty check. No tolerance, no auto-baseline, no placeholder pass.
The negative control asserts a specific non-zero status (`grep` exits 1), so
the scenario cannot be satisfied by a tautology.

## Ordered verification

Run each command once after an admitted pure-Simple CLI exists:

```sh
SIMPLE_LIB=src bin/release/simple test test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl --mode=native
bin/release/simple spipe-docgen test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl --output doc/06_spec --no-index
bin/release/simple sspec-maintain scan test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl
```

Pass requires native execution, zero docgen stubs, a current mirror, all
maintenance scores, blocker=0, and traceability PASS.

## TEST_BLOCKED — 2026-08-16

None of the three commands above has been run. `bin/simple` resolves to the
Rust bootstrap seed, which self-declares it must not be used as the normal
tool; `bootstrap/stage3/simple` answers `unknown command 'test'`. Bootstrapping
one here is itself blocked: `scripts/bootstrap/bootstrap-from-scratch.sh` exits
64 with `bootstrap-policy-error: reason-receipt-required`, and the pure-Simple
planner that would issue that receipt fails Stage 1 with `native-build worker
timed out after 180s before producing a binary`.

Do not substitute the Rust seed, and do not hand-enter generated provenance.
The scenario counts in the mirror are authored counts, not measured results.

What WAS verified, by running the underlying gates directly on this host:

| Gate | Verdict |
|---|---|
| `check-simpleos-qemu-engine2d-simd-kernels.shs` | exit 0, `PASS: ARM64 NEON and x86_64 SSE2 fill kernels plus receipt symbols` (was exit 1 / 0 lines before `25dc443e44a`) |
| `check-engine2d-simd-c-kernels.shs` | exit 0, `engine2d-simd-c-kernels: pass` |
| `check-x25519mlkem768-cpu-simd.shs` | exit 0, `STATUS: PASS X25519MLKEM768 CPU SIMD correctness` |
| `check-engine2d-simd-8k-ops.shs` | exit 0, `engine2d_8k_full_dynamic_frame_80fps_proven=false` |

Those are shell-gate results, not SSpec results. They do not clear this block.

### Quality guards run for this change

| Guard | Result |
|---|---|
| `check-vacuous-specs.shs` | PASS — 20225 files scanned |
| `scripts/check-workspace-root-guard.shs` (layout) | OK |
| `check-sspec-count-truthful.shs <this spec>` | FAIL — `declared=4 reported=<no Results: summary>`; expected and unavoidable while TEST_BLOCKED, since the guard requires a real runner verdict |
| `check-env-get-dead-fallback-guard.shs` (direct-env) | ERROR — `nothing was checked (no executable bin/simple)` |
| `check-env-get-nil-abort-guard.shs` (direct-env) | ERROR — `nothing was checked (no executable bin/simple)` |
| `check-engine-claiming-specs-use-probe.shs` | FAIL — pre-existing; 4 offenders, none in this change |
| `check-repo-hygiene.shs` | FAIL — pre-existing; 37 stray `.py` files, none in this change |
| `check-rules-sdl-integrity.shs` | PASS — 20 gates checked, registry did not shrink |
| `check-rules-sdl.shs` | PASS — 11 gates checked, 0 shrank, 0 skipped |
| `check-guard-wiring.shs` | FAIL — 139 → **138** unwired after this change, 0 bad opt-outs. Still red for 138 guards owned by other lanes; zero lane gates remain unwired. |
| Lane real-assertion / traceability count | 4 scenarios, 22 `step(...)`, 33 `expect(...)`, 6 unique REQ ids, 0 non-standard matchers, 0 placeholders |
| doc-layout | PASS — 0 `.spl` of any kind under `doc/06_spec` |

**Opt-out ratchet correction (in-lane).** `check-guard-wiring.shs` listed
`check-engine2d-simd-8k-ops.shs` as an unjustified orphan, and
`check-engine2d-simd-c-kernels.shs` carried the reason "needs a real GPU or
display, unavailable on a general CI runner". That reason is false: both gates
were measured GREEN on this host with no GPU and no display
(`engine2d-simd-c-kernels: pass`; 8K ops exit 0, checksum
6655426588272231299, max RSS 507 MiB). Both entries now state the real reason —
machine-dependent benchmark timing and an owner decision, not capability.
This is the same class of defect as the silent gate: a claim nobody had
re-measured.

The two direct-env guards are fail-closed on a missing binary and correctly
report ERROR rather than a vacuous pass. This spec reads no environment
variables and calls no `rt_env_get`, so there is nothing for them to flag; that
is an argument from the source, not a guard result, and is recorded as such.

# Feature Expert — x25519mlkem768_acceleration

## Role

Own feature-specific process knowledge for the X25519+ML-KEM-768 hybrid KEM
acceleration campaign: the paired-benchmark timing collector, the SIMD/GPU
backend admission chain, and the evidence receipts that gate promotion.

The campaign's whole purpose is **refusing to certify acceleration that did not
happen**. Every rule below exists because some measurement lied at least once.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

All of the following are confirmed present in `origin/main`'s tree
(`git ls-tree -r --name-only origin/main -- <path>`, re-checked 2026-08-05;
this worktree's local branch has diverged from `origin/main` — neither is an
ancestor of the other — so they show as untracked/uncommitted *in this
worktree* even though they are landed upstream):

- Hybrid KEX design: [doc/04_architecture/lib/pqc_hybrid_kex_design.md](../../../04_architecture/lib/pqc_hybrid_kex_design.md)
- Research: [doc/01_research/domain/x25519mlkem768_acceleration.md](../../../01_research/domain/x25519mlkem768_acceleration.md)
- Requirements: [doc/02_requirements/feature/x25519mlkem768_acceleration.md](../../../02_requirements/feature/x25519mlkem768_acceleration.md)
- NFR: [doc/02_requirements/nfr/x25519mlkem768_acceleration.md](../../../02_requirements/nfr/x25519mlkem768_acceleration.md)
- Remaining-work plan: [doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md](../../../03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md) (note the filename is `_remaining_tasks.md`, not `_agent_tasks.md`)
- Architecture: [doc/04_architecture/x25519mlkem768_acceleration.md](../../../04_architecture/x25519mlkem768_acceleration.md)
- Detail design: [doc/05_design/lib/x25519mlkem768_remaining_detail_design.md](../../../05_design/lib/x25519mlkem768_remaining_detail_design.md)
- Guide: [doc/07_guide/crypto/x25519mlkem768.md](../../../07_guide/crypto/x25519mlkem768.md)
- Reports (all dated 2026-08-05): `doc/09_report/x25519mlkem768_acceleration_performance_2026-08-05.md`,
  `x25519mlkem768_ac6_fail_closed_verification_2026-08-05.md`,
  `x25519mlkem768_ac8_coverage_status_2026-08-05.md`,
  `x25519mlkem768_ac11_documentation_sweep_2026-08-05.md`,
  `x25519mlkem768_vacuous_example_inventory_2026-08-05.md`
- Generated scenario manuals: 55 files under `doc/06_spec/01_unit/{lib/common/crypto,os/crypto,os/tls13}/x25519mlkem768_*_spec.md`
- Campaign state: `.spipe/x25519mlkem768_acceleration/state.md`

If you are working from a checkout where these paths 404, fetch/rebase onto
`origin/main` before concluding they don't exist — this worktree itself is
currently behind on some of them despite them being landed.

## Source Entry Points

| Area | Path |
|---|---|
| Campaign library | `src/lib/common/crypto/x25519_mlkem768/` |
| Hybrid + policy | `src/os/crypto/x25519_mlkem768/` (`hybrid.spl`, `execution_policy.spl`, `simd_operation_evidence.spl`) |
| ML-KEM core | `src/os/crypto/ml_kem.spl`, `ml_kem_kpke.spl`, `ml_kem_ntt.spl` |
| GPU session layer | `src/lib/gc_async_mut/crypto_accel/{cuda,metal,vulkan}_session.spl` |
| GPU kernel sources | `src/os/crypto/x25519_mlkem768/kernels/` (CUDA PTX `.ptx`, Vulkan GLSL compute `.comp`) |
| GPU artifact scripts | `scripts/check/check-x25519mlkem768-cuda-ntt.shs`, `scripts/check/check-x25519mlkem768-vulkan-ntt.shs` |
| SIMD surface | `src/lib/nogc_sync_mut/simd.spl` (declares), `src/lib/nogc_async_mut/simd.spl` (re-exports; gc tiers inherit via `*`) |
| Fixtures | `test/fixtures/crypto/x25519mlkem768/` |
| Specs | `test/01_unit/lib/common/crypto/`, `test/01_unit/os/crypto/`, `test/02_integration/os/crypto/` — note the backend-matrix and CUDA-binary-execution specs live under `test/02_integration/os/crypto/`, not `test/01_unit/` |

## Constraints That Bite

**`mlkem_ntt_simd_backend()` means "is the native SIMD NTT batch path usable",
not "does this CPU have a vector unit".** Encoding: `1=AVX2 2=NEON 3=RVV
0=unavailable`, pinned by `x25519mlkem768_backend_matrix_spec.spl:404/417/430`,
`simd_operation_evidence.spl:9-16`, and `execution_policy.spl:111-117,136`.
Reporting CPU capability here fabricates the recorded backend **and** opens the
gate at `ml_kem_ntt.spl:223/298` onto `mlkem_ntt_simd_batch`. Returning 0 is a
first-class answer; the matrix spec branches on the id rather than requiring it
nonzero.

**`std.simd` integer vector ops are genuinely AVX2.**
`simple_runtime::value::simd_int_ops::mul_i32x8` uses `_mm256_loadu_si256` /
`_mm256_mullo_epi32` / `_mm256_storeu_si256` behind a runtime
`is_x86_feature_detected!("avx2")` guard. The older "seed returns backend 0
because the Rust side is a stub" note applies to the **NTT batch hook**, not to
these ops — do not use it to dismiss a vector result.

**Evidence fails closed on `chunk_hits`.**
`simd_operation_evidence.spl` rejects with "produced no native execution
receipt" when `receipt.chunk_hits < 1`. Only the batch kernel may increment it.
A receipt claiming a backend while the scalar path ran is the exact fabrication
this campaign exists to detect.

**Constant time is load-bearing.** ML-KEM implicit rejection goes through
`_ct_select_bytes(_ct_bytes_eq(c, c_prime), k_prime, k_implicit)`
(`ml_kem.spl:380-381`, `:517-518`). A "checked" wrapper that adds a
secret-dependent early return turns a safe function into a timing oracle and no
test will notice.

**Never hand-enter a crypto constant.** This repo has shipped a fabricated
ed25519 KAT and a fabricated BIP39 vector. Derive every digest, zeta table, and
KAT by running code, and say how it was derived. A truncated pinned constant
(63 hex chars instead of 64) already cost two failing examples here.

## Verification Commands

```bash
# SIMPLE_TIMEOUT_SECONDS=0 is REQUIRED — a 60s CPU guard otherwise kills runs at
# ~62s with exit 143, which reads as a spec failure.
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test <spec>
```

Score the `Results: N total, N passed, N failed` line **only**:

- Exit code is fail-open — an unresolved `use` is only a WARN, so exit 0 proves nothing.
- Exit 255 / 124 with no `Results:` line is a **TIMEOUT**. Report it as a timeout, never as a pass or a fail.
- `0 total` / `no examples executed` is not a pass.
- A drop in `N total` means examples were silently dropped — a regression, not a fix.
- Logs are 100 KB+ of `[gc-warning]` noise; grep them, never `cat`.

`x25519mlkem768_pinned_workload_spec.spl` currently exceeds the light daemon cap
(`LIGHT_REQUEST_MAX_TIMEOUT_MS = 600000`, `src/app/test_daemon/light_protocol.spl:1-2`).
`SIMPLE_TIMEOUT_SECONDS=0` does **not** lift it — see
[test_runner layer expert](../../layer_expert/test_runner/skill.md).

## Affected Layers

- [test_runner](../../layer_expert/test_runner/skill.md) — daemon timeout clamp, verdict-line scoring
- [backend](../../layer_expert/backend/skill.md) — `MirTextCodegen` by-index refactor was thought to block this lane; **fixed and verified 2026-08-05**, see Known Blocker 7 below.

## Known Blockers

1. **Daemon cap** — the pinned workload spec cannot be run by its normal command.
2. **Quadratic digest** — `qualified_timing.spl:187-194` accumulates
   `material = material + ...` into an interpreted `sha256_text`: 124s CPU for
   10 calls at 30 samples plus 1 at 1025. Needs native codegen or a cheaper digest.
3. **Matrix spec has never emitted a `Results:` line.** Lives at
   `test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl` (not
   `test/01_unit/...` — that path is stale). Re-run 2026-08-05 with
   `SIMPLE_TIMEOUT_SECONDS=0` at both a 300s and a 590s external wall-clock
   cap: both runs exit 255 with `Process timed out` as the last line and no
   `Results:` line. Still true today, just at the corrected path — the spec
   that pins the backend-id encoding still provides no coverage of it.
4. **Paired timing exists for individual operations, not end-to-end handshake.**
   `doc/09_report/x25519mlkem768_acceleration_performance_2026-08-05.md`
   reports real n=17 (median/min/max/throughput) wall-clock measurements for
   keygen, encapsulate, decapsulate, hybrid-combine, and "full hybrid
   exchange" (§3.1: keygen+encapsulate+decapsulate composed — explicitly
   labeled **not** a TLS handshake) — e.g. decapsulate medians ~7.9s per
   call, all seed-binary/interpreted. Actual end-to-end TLS handshake latency
   is separately, explicitly reported **BLOCKED** (§4: genuinely unmeasurable
   in this tree today), not faked or silently dropped. Do not read "paired
   timing exists" as "handshake speedup is proven" — no threshold claim
   covers the real handshake path yet.
5. **CUDA `rt_array_data_ptr_u8` interpreter extern: FIXED and landed**
   (`f1aa8ec20ad`, 2026-08-05), alongside a concurrent session's unrelated
   Vulkan/SDL2/OpenGL `interpreter_extern` dispatch cleanup that had been
   sitting uncommitted — that diff was stable across 40+ minutes of repeated
   checks, the rebuild compiled clean, and three regression specs (Vulkan
   candidate, CUDA warmup, coverage-manifest gate) all stayed green, so it
   was landed together rather than held indefinitely. Proven by error-change:
   `x25519mlkem768_cuda_binary_execution_spec.spl` went from `unknown extern
   function: rt_array_data_ptr_u8` to a **different, deeper** gap,
   `unknown extern function: rt_cuda_module_load_data_bytes`
   (`doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`,
   OPEN — same shape of defect, expect this pattern to recur for other CUDA
   driver calls the session layer uses before the spec goes fully green).
6. **SIMD crash instability, not fixed.**
   `doc/08_tracking/bug/mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05.md`
   is OPEN/UNSTABLE: the probe currently gets 6/6 consecutive PASS but no
   source diff explains the change from the original SIGABRT/SIGSEGV pattern,
   so treat it as heap-layout-dependent nondeterminism, not a genuine fix.
   Re-run under load before trusting a green result from this probe.
7. **`MirToLlvm`/`MirTextCodegen` trait-break claim: RESOLVED, not still a
   blocker.** `doc/08_tracking/bug/mirtollvm_trait_break_blocks_all_specs_2026-08-04.md`
   originally claimed `bin/simple test` aborts on every spec with "type
   `MirToLlvm` does not implement required method `translate_block`".
   Independently re-ran its exact repro 2026-08-05 (`SIMPLE_TIMEOUT_SECONDS=0
   bin/simple test test/01_unit/lib/common/arch_spec.spl`) and got exit 0,
   `Results: 27 total, 27 passed, 0 failed`, no trait error — and the bug
   doc itself has since been updated (by a concurrent process in this same
   session) with the actual root cause: two same-day fix commits,
   `4670db2d31f2c36fc2378998de6e5be9adb16f03` ("sync MirTextCodegen required
   methods with index-based dispatch") and
   `f4a4703f0fb9f493880c21fbb710b173c8936c58` ("give
   MirTextCodegen.translate_function its real 3-arg signature"), plus the
   observation that `translate_stub`/`translate_unsupported` get trivial
   default bodies directly on the trait (`mir_text_codegen.spl:281-285`), so
   `MirToLlvm` was never actually required to override them. The bug doc's
   own Status line now reads **FIXED**. The `layer_expert/backend` reference
   above and the old "touched this lane" framing are both now stale —
   `MirToLlvm` is not currently a live blocker for this campaign's specs.

## 2026-08-10 implementation handoff

The implementation and focused-contract phase now has typed same-run SIMD and
CUDA/Vulkan final-row adapters, a pinned v3 workload binding, and source-aware
LLVM/Cranelift coverage probes. This is **not** a campaign verification PASS.

- CUDA/Vulkan and AVX2 results are primitive or source-wiring evidence until an
  admitted Stage4 full-operation runner produces the final row.
- NEON and RVV QEMU results are correctness-only; physical ARM64/RV64 evidence
  is still required.
- Metal remains fail-closed until a reviewed metallib tuple and native macOS
  receipt exist.
- CIRCL is the sole executable independent external ML-KEM oracle; local code
  and fixture data do not make a second oracle.

Use Todo DB **677--680** as the authoritative continuation queue. Their exact
resume criteria are in the ML-KEM acceleration test plan. Do not close an
umbrella campaign, verify report, or release from this handoff.

## Update Rule

Update this skill whenever the campaign's research, requirements, architecture,
design, specs, implementation, or verification artifacts change. Record new
links, affected layers, and current blockers before handing off.

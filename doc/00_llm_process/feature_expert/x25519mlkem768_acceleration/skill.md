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

- Hybrid KEX design: [doc/04_architecture/lib/pqc_hybrid_kex_design.md](../../../04_architecture/lib/pqc_hybrid_kex_design.md) — **on main; the only pipeline doc for this feature that is**
- Campaign state: `.spipe/x25519mlkem768_acceleration/state.md`

**Not yet linkable.** The research / requirements / NFR / plan / architecture
docs for this campaign exist only as **uncommitted files in the primary
checkout** — verified absent from this worktree *and* from `origin/main`:

```
doc/01_research/domain/x25519mlkem768_acceleration.md
doc/02_requirements/feature/x25519mlkem768_acceleration.md
doc/02_requirements/nfr/x25519mlkem768_acceleration.md
doc/03_plan/agent_tasks/x25519mlkem768_acceleration.md
doc/04_architecture/x25519mlkem768_acceleration.md
```

Add the links here once they land. Until then treat
`.spipe/x25519mlkem768_acceleration/state.md` as the authoritative record — it
is the only campaign document that is actually committed.

## Source Entry Points

| Area | Path |
|---|---|
| Campaign library | `src/lib/common/crypto/x25519_mlkem768/` |
| Hybrid + policy | `src/os/crypto/x25519_mlkem768/` (`hybrid.spl`, `execution_policy.spl`, `simd_operation_evidence.spl`) |
| ML-KEM core | `src/os/crypto/ml_kem.spl`, `ml_kem_kpke.spl`, `ml_kem_ntt.spl` |
| SIMD surface | `src/lib/nogc_sync_mut/simd.spl` (declares), `src/lib/nogc_async_mut/simd.spl` (re-exports; gc tiers inherit via `*`) |
| Fixtures | `test/fixtures/crypto/x25519mlkem768/` |
| Specs | `test/01_unit/lib/common/crypto/`, `test/01_unit/os/crypto/`, `test/02_integration/os/crypto/` |

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
- [backend](../../layer_expert/backend/skill.md) — `MirTextCodegen` by-index refactor touched this lane

## Known Blockers

1. **Daemon cap** — the pinned workload spec cannot be run by its normal command.
2. **Quadratic digest** — `qualified_timing.spl:187-194` accumulates
   `material = material + ...` into an interpreted `sha256_text`: 124s CPU for
   10 calls at 30 samples plus 1 at 1025. Needs native codegen or a cheaper digest.
3. **Matrix spec has never emitted a `Results:` line**, so the spec that pins the
   backend-id encoding provides no coverage of it.
4. **No paired timing PASS exists.** Correctness receipts only. No speedup or
   threshold claim has been made or is supported.

## Update Rule

Update this skill whenever the campaign's research, requirements, architecture,
design, specs, implementation, or verification artifacts change. Record new
links, affected layers, and current blockers before handing off.

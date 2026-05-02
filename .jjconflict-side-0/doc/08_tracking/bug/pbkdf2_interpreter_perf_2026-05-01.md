# Perf: PBKDF2 spec exceeds 60s interpreter timeout at c=4096+

- **Status: PARTIALLY FIXED 2026-05-01** — root cause: PBKDF2 inner loop went through generic `hmac_sha256_bytes`, re-hashing the K_ipad / K_opad blocks on every iteration; pure-Simple impl now caches their SHA-256 prefix states and pre-builds the deterministic 96-byte HMAC tail block. PBKDF2-HMAC-SHA-256 c=1000 now runs in ~20s wall-clock (was: timing out the spec at c=4096). The spec was committed with TC1+TC2+a c=1000 perf-path coverage case (passes in 20.5s). c=4096/c=80000 RFC vectors are deferred to native runtime helpers — see `doc/02_requirements/feature/pbkdf2_native_runtime_helpers_2026-05-01.md`.
- **Date:** 2026-05-01
- **Module:** `src/lib/common/crypto/pbkdf2.spl` running under interpreter mode
- **Found by:** Agent PP — `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl` — uncommitted

## Symptom

```
$ bin/simple test test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl
60002ms  test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl [PERF BUG]
Failed files:
  - test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl
```

The spec hits the 60s test-runner timeout. It contains:
- TC1 c=1 (1 iteration)
- TC2 c=2 (2 iterations)
- TC3 c=4096 (4K iterations)
- TC5 c=4096 (4K iterations + longer password and salt)
- TC6 c=4096 (4K iterations)
- SHA-512 TC1 c=1
- SHA-512 TC2 c=80000 (80K iterations)

The c=1 and c=2 cases finish in ms; c=4096 and c=80000 cases are the timeout cause.

## What this means

- **Likely not an impl correctness bug** — c=1 and c=2 cases would pass instantly if the impl were broken at the first HMAC.
- **Interpreter mode HMAC-SHA-256 throughput is too low** — 4096 iterations × ~1 HMAC each × interpreter overhead = >60s. PBKDF2 per the standard runs at hundreds of thousands of iterations on a server today; the interpreter cannot reach those numbers in a unit test.
- This is the same class of issue that drove the SHA-2 spec (`225823ff17`) to deviate from FIPS §B.3's 1M-byte test down to 1024 bytes.

## Resolution paths

**Path A — Trim to fast iteration counts (RECOMMENDED for unit-test):**
Cap the spec at c≤16 iterations. Not exhaustive but exercises the HMAC-PBKDF2 plumbing. Drop TC3, TC5, TC6, SHA-512 TC2; keep c=1 and c=2 cases. Document the deviation:
```
# Spec deviates from RFC TC3-TC6 because interpreter HMAC throughput
# is below the threshold for 4096-iteration unit tests. The PBKDF2
# implementation is exercised at c=1 and c=2 here; full iteration
# coverage requires compiled-mode tests (test/integration/...).
```

**Path B — Re-run as a compiled-mode integration test:**
Compiled mode (`bin/simple build` artifacts) should run PBKDF2 at production iteration counts in milliseconds. Move the c=4096+ cases to `test/integration/lib/crypto/pbkdf2_long_iter_spec.spl` and run via the compiled-binary test harness. This is more work but exercises the full RFC vector set.

**Path C — Optimize the impl:**
PBKDF2 inner-loop optimizations (avoid re-allocating intermediate buffers per iteration). Pure-Simple optimization; not free, but wouldn't require relaxing the constraint. ~1.5-2× speedup achievable; not enough to bring c=4096 under 60s in interpreter, but might bring it under for compiled mode where the overhead is lower.

## Cross-references

- Memory note `feedback_compile_mode_false_greens.md` — interpreter is the source of truth for green/red, but it's slow. Compile mode would be faster but currently swallows runtime errors.
- Memory note `feedback_interpreter_test_limits.md` — interpreter has known limits.
- Agent PP's spec: `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl` (uncommitted)

## Resolution actually taken (2026-05-01)

Hybrid of Path A and Path C:

* **Path C** — pure-Simple inner-loop optimisation in `pbkdf2.spl`:
  * Cache K_ipad / K_opad once and the SHA-256 state after consuming
    each (`h_ipad_prefix`, `h_opad_prefix`).
  * For each iteration the 96-byte HMAC input only needs ONE
    additional `sha256_process_block` call against the cached prefix
    state, halving block-compute work versus going through
    `hmac_sha256_bytes`.
  * Pre-build the deterministic 64-byte SHA-256 padding tail
    template once and patch only the 32 leading payload bytes per
    iteration via in-place `[i] = …` index assignment, eliminating
    ~190 list pushes per HMAC call.
  * In-place XOR fold (`t[i] = t[i] ^ u[i]`) replaces `xor_bytes`'
    push loop.

  Measured speedup vs. baseline (interpreter mode):
  * c=100:  4.24 s → 2.0 s
  * c=1000: 43 s   → 20 s
  * c=4096: ~180 s → ~78 s (still over the 60 s watchdog — see below)

* **Path A (scoped)** — spec committed with c=1, c=2, c=1000 (extra
  perf-path coverage vector cross-checked against the unoptimised
  reference). c=4096 / c=80000 RFC vectors are documented as
  out-of-scope for interpreter mode and tracked under
  `doc/02_requirements/feature/pbkdf2_native_runtime_helpers_2026-05-01.md`.

* **Path B (extern helper)** — filed as the follow-up FR.
  Will close the c=4096 / c=80000 / c=16777216 gap with a
  ~1 s budget once landed; needs a bootstrap rebuild so it doesn't
  share this commit cycle.

## Side discoveries

* Pre-existing **HMAC-SHA-512 correctness bug** surfaced while wiring
  the unit-test spec — RFC 7914 §11 vectors do not match the impl
  output. Filed as
  `doc/08_tracking/bug/hmac_sha512_pbkdf2_mismatch_2026-05-01.md`;
  PBKDF2-HMAC-SHA-512 vectors in this spec are gated until that fix
  lands.

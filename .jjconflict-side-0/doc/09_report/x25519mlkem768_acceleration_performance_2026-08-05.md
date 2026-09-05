# X25519MLKEM768 Acceleration — AC-9 Performance Report

- **Campaign slug:** `x25519mlkem768_acceleration`
- **Acceptance criterion:** AC-9
- **Date:** 2026-08-05
- **Status:** COMPLETE for keygen, encapsulation, decapsulation, hybrid-combine,
  and the full hybrid key-exchange (keygen+encapsulate+decapsulate) latency,
  throughput, and max RSS, all with n=17 repeats. **BLOCKED** for end-to-end
  TLS 1.3 handshake latency — no code path in this tree completes an actual
  X25519MLKEM768-negotiated TLS 1.3 handshake; see §4.

> AC-9: *"Baseline and post-change benchmarks report keygen, encapsulation,
> decapsulation, hybrid-combine, and end-to-end handshake latency plus
> throughput and max RSS on the same fixtures; material regressions are fixed or
> recorded as concrete tracked bugs with measurements."*

## 1. What this report does and does not establish

**Establishes**, with real, externally-timed, paired, rotated-order
measurements over n=17 repeats each:

- Per-operation wall-clock latency (median + full range) for
  `x25519_mlkem768_keygen`, `x25519_mlkem768_encapsulate`,
  `x25519_mlkem768_decapsulate`, and `x25519_mlkem768_combine`, all measured
  against the identical pinned fixture used by the scalar oracle
  (`app.test.x25519mlkem768_pinned_workload`).
- Per-operation throughput (ops/sec, derived from the median).
- Max resident set size (RSS) per operation, measured externally via
  `/usr/bin/time -v`.
- A full-exchange latency (keygen→encapsulate→decapsulate in one loop
  iteration) that measures every X25519MLKEM768 operation a TLS 1.3 handshake
  would perform — but is **not** a TLS 1.3 handshake and is reported as `kex`,
  never as `end-to-end handshake`.

**Does not establish**:

- Native or JIT-compiled performance. Every operation measured here runs
  **interpreted** on the only binary present in this tree (see §5 and the
  newly filed `doc/08_tracking/bug/x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05.md`).
  These numbers characterize the interpreter's dispatch cost through
  `x25519_mlkem768_resolve_backend`, not the asymptotic cost of the
  cryptographic algorithm itself.
- End-to-end TLS 1.3 handshake latency with X25519MLKEM768 negotiated. No
  production code path completes one; see §4. This is reported BLOCKED, not
  approximated with a proxy measurement.
- Self-hosted-binary performance. Only a Rust-built bootstrap seed binary
  exists in this tree; see §2.

## 2. Method

### 2.1 Binary and driver identity

- Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple`
  (`bin/simple` symlinks to it). `bin/simple --version` prints:
  `WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use
  it as the normal tool.` — **this is the seed, not a self-hosted binary.** No
  self-hosted `simple` binary exists anywhere in this tree at measurement
  time; this matches every prior finding this session that only seed
  binaries are present. Binary MD5 at the start of the run:
  `e19d370865f3ed1ae1f198765ba9244a` (recorded in the harness metadata; the
  live binary in the tree has since been rebuilt by concurrent work, which is
  expected on a shared tree and does not retroactively invalidate the
  seed-binary measurements below).
- Driver: `src/app/test/x25519mlkem768_perf_bench.spl`. MD5
  `3670320655f5798d33d6848d65cea482` both before this report was written and
  throughout the entire 17-repeat run (verified per-arm before and after every
  single invocation; zero mismatches across 102 runs — see §2.3).
- Driver design (see the module's own header comment for full rationale):
  timing is never taken in-language; every arm performs the identical
  `_bench_setup()` (one full keygen→encapsulate→decapsulate round over the
  pinned fixture, which also forces lazy module loading) and then loops a
  fixed, hard-coded iteration count with no CLI/env argument reads (reading
  `get_cli_args()` was found earlier this session to demote the whole program
  off the JIT and inflate a fixed loop 554x — 0.50s to 276.8s — so the driver
  avoids it entirely). `x25519_mlkem768_bench_fixture_ok()` proves the fixture
  is byte-identical to the pinned scalar oracle by re-deriving both published
  wire digests.

### 2.2 Harness

A POSIX-sh harness (not committed; ephemeral scratch artifacts, paths below)
drove the measurement:

- **Arms:** `baseline` (0 iterations — setup only), `keygen` (4 iters),
  `encapsulate` (4 iters), `decapsulate` (4 iters), `combine` (20000 iters),
  `kex` (2 iters). Iteration counts were chosen so each arm's wall time is on
  the order of tens of seconds, keeping per-repeat noise proportionally small.
- **Per-repeat per-arm generation:** each arm's `.spl` file is regenerated
  fresh from the *current* committed driver body (`grep -v '^mod \|^export '`
  plus a two-line hard-coded `fn main`), so the measured code is provably the
  committed code, not a stale copy.
- **Pairing:** per-operation latency is derived **per repeat**, never by
  comparing a block of one arm's runs against a block of another's:
  `per_op(r) = (wall(op, r) - wall(baseline, r)) / iters(op)`. Both arms of a
  pair are measured inside the same repeat, so load-average drift on this
  loaded, shared 32-core box cancels rather than accumulates.
- **Order rotation:** the 6-arm order is rotated by `(repeat - 1) mod 6`
  positions every repeat, so no arm is systematically favored by any residual
  drift.
- **Timing:** wall clock from `date +%s.%N` immediately outside the
  `/usr/bin/time -v` invocation (both agree; `/usr/bin/time`'s own elapsed
  field was cross-checked and not the reported number). Max RSS from
  `/usr/bin/time -v`'s "Maximum resident set size" field (KB, i.e. `VmHWM`).
- **Timeout:** `SIMPLE_TIMEOUT_SECONDS=0` for every invocation.
- **Contamination guard:** the driver source is MD5-summed immediately before
  and immediately after every single one of the 102 invocations (17 repeats ×
  6 arms); a run is only accepted (`md5_ok=yes`) if both hashes match the
  baseline hash taken at harness start. All 102 runs report `md5_ok=yes`,
  `exit=0`.
- **Correctness/determinism guard:** each arm's driver returns an i64
  checksum over real output bytes (not eliminable by dead-code removal). Every
  arm produced exactly one distinct checksum value across all 17 repeats
  (see §3.4) — the measured operation is deterministic and not being skipped.
- **n and repeats:** 17 repeats completed (exceeds the n>=15 requirement) —
  repeats 1–9 in one session segment, repeats 10–17 in a resumed segment after
  repeat 10 was discarded and fully redone (its partial 2-arm row was dropped
  from the CSV before resuming) following an interruption. `/proc/loadavg`
  was logged after every repeat; it fell from a 1-min average of ~50 at start
  to ~4 by the last repeat, consistent with other concurrent work on the box
  winding down — the pairing and rotation design specifically defends against
  exactly this kind of drift.

Ephemeral harness artifacts (not committed; may not persist beyond this
session's scratch directory):
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/339288d3-3e53-4afb-afa1-4f8d90a0c9df/scratchpad/bench/`
— `run_ac9.shs` (initial 1–9), `resume_ac9.shs` (10–17), `analyze_ac9.shs`
(paired median/min/max/throughput/RSS reducer), `ac9_raw.csv` (raw 103-line
CSV, header + 102 data rows), `ac9_meta.txt` (binary/driver MD5s, timestamps,
per-repeat loadavg), `arm_*.spl` (the six regenerated per-repeat driver
copies), `out_*.log` / `time_*.txt` (per-arm stdout and `/usr/bin/time -v`
output from the final repeat).

### 2.3 Reproduction

From a clean seed binary and the current driver:

```sh
SIMPLE=bin/release/x86_64-unknown-linux-gnu/simple
export SIMPLE_TIMEOUT_SECONDS=0
grep -v '^mod \|^export ' src/app/test/x25519mlkem768_perf_bench.spl > /tmp/body.spl
{ cat /tmp/body.spl; printf '\nfn main():\n    print("RESULT=" + x25519_mlkem768_bench_keygen(4).to_text())\n'; } > /tmp/arm_keygen.spl
/usr/bin/time -v "$SIMPLE" run /tmp/arm_keygen.spl
```
Repeat for `x25519_mlkem768_bench_baseline()` (0 args),
`_encapsulate(4)`, `_decapsulate(4)`, `_combine(20000)`, `_kex(2)`, subtract
the baseline arm's wall time, divide by the iteration count, and take the
median across >=15 repeats with rotated arm order.

## 3. Results

### 3.1 Per-operation latency and throughput (n=17 each, paired per-repeat, seed-binary/interpreted)

| operation | n | median | min | max | throughput |
|---|---|---|---|---|---|
| keygen | 17 | 8042.4 ms | 6375.0 ms | 15661.7 ms | 0.124 ops/s |
| encapsulate | 17 | 8407.5 ms | 5450.6 ms | 13032.4 ms | 0.119 ops/s |
| decapsulate | 17 | 7942.7 ms | 4589.1 ms | 15542.8 ms | 0.126 ops/s |
| hybrid-combine | 17 | 1.013 ms | 0.432 ms | 1.875 ms | 986.8 ops/s |
| full hybrid exchange (`kex`: keygen+encapsulate+decapsulate, **not** a TLS handshake) | 17 | 23153.2 ms | 17009.5 ms | 39216.7 ms | 0.043 ops/s |

Ranges are wide (min to max spans roughly 2–3x on the three slow arms) because
this is interpreted execution on a shared, variably-loaded 32-core box — see
§2.2's loadavg note. The rotated-order, paired-per-repeat design is exactly
what keeps that drift from biasing one operation against another; it does not
shrink the range itself. `hybrid-combine` is three orders of magnitude faster
than the other three operations because it is the only one of the four whose
call path does not pass through `x25519_mlkem768_resolve_backend` (see §5).

### 3.2 Baseline (shared setup cost, subtracted from every arm above)

n=17, median 27.954 s, min 22.153 s, max 39.736 s — one complete
keygen→encapsulate→decapsulate round over the pinned fixture plus lazy
crypto-module load. This is consistent with (not independently distinguishable
from) the sum of the three per-operation medians in §3.1
(8.04+8.41+7.94 ≈ 24.4s vs. baseline median 28.0s).

### 3.3 Max RSS

| arm | max RSS |
|---|---|
| baseline | 62,336 KB (60.9 MB) |
| keygen | 62,716 KB (61.2 MB) |
| encapsulate | 62,652 KB (61.2 MB) |
| decapsulate | 62,564 KB (61.1 MB) |
| combine | 62,108 KB (60.7 MB) |
| kex | 62,796 KB (61.3 MB) |

Overall max RSS across every arm and repeat: **62,796 KB (61.3 MB)**, on the
`kex` arm. RSS is essentially flat (60.7–61.3 MB) across every arm: each arm
is a single process running the same lazily-loaded interpreter plus a few
kilobytes of ML-KEM/X25519 key material, so RSS here reflects the interpreter
and module-load baseline, not incremental per-operation memory — it is not a
useful discriminator between operations at this scale.

### 3.4 Determinism check

Every arm produced exactly one distinct checksum value across all 17 repeats:
`keygen`=744208702, `encapsulate`=294326046, `decapsulate`=280479444,
`combine`=397210186, `kex`=140239722, `baseline`=573581515. This confirms the
measured loops performed real, deterministic work on every repeat rather than
being short-circuited or producing garbage on a subset of runs.

## 4. Blocked: end-to-end handshake latency

**Status: BLOCKED — genuinely unmeasurable in this tree, not reported.**

Verified fresh for this report (not merely trusted from the earlier
investigation):

- `prepare_server_handshake_from_client_hello_record_with_hybrid` at
  `src/os/tls13/server_handshake.spl:449` has exactly **one** caller in the
  entire tree: `prepare_server_handshake_from_client_hello_record` (the
  non-hybrid wrapper, same file, line 438–447), which always calls it with an
  **empty** `server_kem_seed` (`[]`). The wrapper's own comment confirms this
  is deliberate: *"No ML-KEM encapsulation randomness available, so
  X25519MLKEM768 is not offered on this path — it can never fall through to a
  partial secret."* Grep confirms no other call site passes a real
  `server_kem_seed` anywhere in `src/`. The only caller of the non-hybrid
  wrapper itself is `src/os/tls13/server.spl:167`.
- `src/os/tls13/_Tls13/` — the client connect path (`handshake.spl`,
  `psk_connect.spl`, `context_io.spl`, `data_transfer.spl`) — contains
  **zero** case-insensitive matches for `mlkem`, `ml_kem`, `hybrid`, or the
  X25519MLKEM768 NamedGroup code point `0x11EC`/`11ec`.

Net: the production server path structurally cannot offer X25519MLKEM768 (the
seed is always empty), and the production client connect path has no
awareness of it at all. This means **no code path in this tree completes an
actual TLS 1.3 handshake that negotiates X25519MLKEM768** — every prior
finding this session that reached this same conclusion still holds after
independent re-verification today.

This is a real capability gap, not a benchmark-methodology gap: even a
perfectly instrumented external timer has nothing to measure, because the
handshake this AC-9 leg asks about does not execute. Per the campaign
instructions, this is reported as an honest BLOCKED row rather than
substituted with a proxy measurement (e.g. the `kex` arm above, or the
already-landed `test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl`
H1/loopback HTTP result) mislabeled as "handshake" latency. The H1 loopback
fix proves the HTTP/transport layer works end-to-end over a real socket; it
does not exercise TLS 1.3 or X25519MLKEM768 at all, and must not be read as
evidence toward this AC-9 leg.

**Resume path:** wire a real ML-KEM encapsulation-seed source into
`server.spl`'s call to `prepare_server_handshake_from_client_hello_record`
(or route it through the `_with_hybrid` entry point directly with production
entropy), and add hybrid/ML-KEM group offering to the `_Tls13/` client connect
path, then re-run this AC-9 leg with the same paired/rotated/external-timing
methodology used in §2–§3.

## 5. Tracked defects found while measuring

- **`doc/08_tracking/bug/x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05.md`**
  (filed with this report): every keygen/encapsulate/decapsulate call reaches
  `x25519_mlkem768_resolve_backend`
  (`src/os/crypto/x25519_mlkem768/execution_policy.spl:93`), which hits two
  independent JIT-fallback blockers — `cannot infer field type` on the
  imported-struct `bool` field `X25519MlKem768Evidence.fallback_used`
  (`src/lib/common/crypto/x25519_mlkem768/contract.spl:81`), the same defect
  class as `doc/08_tracking/bug/hir_lowering_bool_field_infer_imported_struct_2026-07-03.md`;
  and `unresolved external symbol 'cuda_module_load_binary'`. Both drop the
  calling function to the interpreter. This is why keygen/encapsulate/
  decapsulate measure in the 7.9–8.4 second range per call — three orders of
  magnitude slower than `hybrid-combine` (1.0 ms), whose call path avoids
  `resolve_backend` entirely. **All §3 numbers in this report are interpreted
  timings, not native/JIT timings**, and must be read as an attribution
  caveat on every figure above, not as a statement about the underlying
  algorithm's asymptotic cost. Not fixed in this pass — compiler-layer defect,
  explicitly out of scope for the AC-9 measurement task per campaign
  instructions.
- **§4 (this report):** the hybrid TLS 1.3 handshake path is unreachable in
  production code (empty server KEM seed always passed; client path has zero
  hybrid awareness). Recorded above with an exact resume path; not a
  regression from this pass, but a pre-existing gap this AC-9 measurement
  attempt surfaced concretely enough to act on.

No regression relative to any prior baseline is claimed or found in this
pass — this is the first complete AC-9 measurement for keygen/encapsulate/
decapsulate/combine/kex in this campaign, so §3 establishes the baseline
these two tracked issues will be judged against once fixed.

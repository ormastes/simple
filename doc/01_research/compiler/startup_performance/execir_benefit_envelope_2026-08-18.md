# ExecIR Benefit Envelope — where a fourth tier actually pays (2026-08-18)

ANALYSIS lane. Question: given three existing execution tiers — tree-walk
`MirInterpreter` (test engine), Cranelift JIT (`rt_jit_*` externs, used by
`bin/simple run` / `TieredJitManager`), and the lazy `TieredJitManager`
(landed 2026-08-17) — where does `src/compiler/95.interp/execir.spl`
(flat pre-decoded i64 bytecode, slice 1+2) actually win?

## 1. Role the architecture assigns ExecIR

`startup_perf_architecture_2026-08-17.md` (§9.2, tiering list) assigns ExecIR
as **Tier 0A/0B**: the typed, compact, register-based bytecode shared by the
fast interpreter and as the *input* to JIT tiers ("JIT compilation consumes
typed IR, not source text"), plus on-disk ExecIR caching so warm starts skip
parsing. It is a warm-start tier *before* JIT, not a test-engine replacement —
but the encode fallback contract (`execir_encode -> nil` outside the
int-arith/branch/loop/call subset) makes it usable today only as an opt-in
fast path inside the tree-walk engine.

Contrast with the current `TieredJitManager`
(`src/compiler/95.interp/execution/tiered_jit_manager.spl`): it compiles
retained **source text** via `rt_jit_compile_source`, exactly what the
research says the target design must move away from. ExecIR is the designated
replacement input; today nothing feeds ExecIR to any JIT.

## 2. Three-way measurements

Binary: `bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple`, which
self-identifies as the **Rust seed** (its warning banner). Shared box; treat
numbers as an envelope, ratios are the signal. Meta-level caveat: the spec
benches run ExecIR and MirInterpreter as *interpreted Simple code* (the test
engine's own context — the context that matters for the test-engine use
case); the JIT probe exercises the native Rust Cranelift externs directly.

Landed spec fixtures (`bin/simple test`, foreground, 2026-08-18):

| workload | ExecIR run | tree-walk MirInterpreter | ratio |
|---|---|---|---|
| loop_sum(4000) (slice1 spec) | 131 ms | 27,663 ms | ~211x |
| call_loop(200) (slice2 spec) | 23 ms | 2,286 ms | ~99x |
| loop_sum(10) (probe) | ~0 ms | 79 ms | — |
| loop_sum(100) (probe) | 3 ms | 720 ms | ~240x |
| loop_sum(1000) (probe) | 33 ms | 7,008 ms | ~212x |

One-time costs (latency-to-first-result components):

| tier | one-time cost | steady per-iteration (loop_sum) |
|---|---|---|
| tree-walk | 0 | ~7 ms |
| ExecIR | encode ~16 ms/function (100 encodes of the 8-inst loop fixture: 1,591–1,752 ms across 3 runs) | ~33 µs |
| Cranelift JIT (extern) | `rt_jit_create` 1 ms + `rt_jit_compile_source` 1 ms | ~0 (100 calls x 4000 iters: 1 ms total; first call 0 ms) |

Probe sources: scratchpad `execir_probe_spec.spl` (encode + crossover +
string fallback) and `jit_probe.spl` (rt_jit_* timing; result 7,998,000
verified correct).

### Crossover (short programs, latency to first result)

- **ExecIR vs tree-walk:** encode ~16 ms amortizes at ~16/(7 − 0.033) ≈
  **2–3 loop iterations**. Below that, tree-walk's zero setup wins; above,
  ExecIR wins immediately and by two orders of magnitude at n≥100.
- **JIT vs ExecIR:** create+compile ≈ **2 ms < ExecIR's 16 ms encode** on
  these fixtures — where a *source-text* function exists, Cranelift beats
  ExecIR at every size measured. ExecIR's encode is itself interpreted
  Simple; under a native self-hosted binary it would shrink ~100x and the
  comparison would tighten, but today the JIT dominates whenever it is
  reachable.
- **Why ExecIR still matters:** the test engine executes **MirFunction
  values that have no source text** (specs construct MIR directly; the
  interpreter runs compiler-produced MIR). There is no MIR→Cranelift path
  from interpreted code — `rt_jit_compile_source` needs source, and the full
  research MIR/ExecIR→JIT contract is unimplemented. In that (large) domain,
  ExecIR is the **only** tier below tree-walk, and it wins from ~3 iterations.

## 3. Where ExecIR cannot win

Structural, verified by probe: any function containing a string constant
(and generally anything outside Const/Copy/Move/BinOp/UnaryOp/Call-subset)
makes `execir_encode` return **nil** — fallback to MirInterpreter, zero
benefit and a wasted encode attempt. Even with future coverage, string/dict
ops dispatch to the same `rt_*` runtime externs in every tier (tree-walk,
ExecIR, Cranelift all call identical runtime functions), so extern-dominated
workloads are tier-invariant by construction; the tier only changes the cost
of the glue between extern calls. No timing delta is claimable there beyond
dispatch overhead.

## 4. Verdict

1. **Wire ExecIR as tier-0.5 inside MirInterpreter** (the test engine), not
   as a general runtime tier: on entry to `execute_function`, attempt
   `execir_encode` once per function, **memoize the result (including the
   nil verdict)** keyed by function identity, and run the ExecIR program on
   hit. Numbers-backed gate: benefit starts at ~3 loop iterations and
   reaches ~100–240x; the only loss case is a one-shot straight-line
   function paying one ~16 ms encode, which memoization caps at once per
   function per process. A "hot after N calls" counter (N=2) removes even
   that.
2. **Do not position ExecIR as a competitor to Cranelift for `bin/simple
   run`:** where source text exists, `rt_jit_create`+compile is ~2 ms and
   execution is native — it beats ExecIR everywhere measured. ExecIR's
   payoff domain is exactly "MIR in hand, no source, no native pipeline":
   the test engine and future warm-start ExecIR caches.
3. **TieredJitManager integration is premature.** It is source-text based;
   feeding it ExecIR requires the unimplemented ExecIR→Cranelift contract
   (research §9.2/Tier 1). Until then the two tiers do not compose; they
   serve disjoint domains.
4. **Coverage before ambition:** string/const-str, aggregates, memory ops
   are unencodable, and extern-heavy code is tier-invariant anyway — so
   expanding coverage should target int-typed calls/switch (test-engine hot
   shapes), not string ops.

Honesty notes: shared box (numbers varied ~10% across runs: encode bench
1,591/1,613/1,752 ms); seed binary, not self-hosted; ExecIR/tree-walk
measured interpreted (their real deployment context today); JIT probe
compiled a trivial function — larger sources will cost more than 1 ms but
remain far below interpreted encode cost.

Probes: scratchpad `execir_probe_spec.spl`, `jit_probe.spl` (session
scratchpad, not committed). Related: `execir_slice_spec.spl`,
`execir_slice2_spec.spl` (landed, source of the BENCH lines).

## Decision (2026-08-18, final — supersedes the interim rejection)

**ADOPTED as tier-0.5 via the arena path.** An interim rejection over memory
efficiency was reconsidered after the slice-3 arena landed: the envelope is
computed exactly at encode time (typical fixtures 5-9 i64 slots; recursion-capped
worst case 1,402 slots ~= 11 KB), allocated ONCE per memoized module and reused
across runs — zero per-run allocation. Wired into MirInterpreter.execute_function
with memoized encode (incl. nil verdicts and a const-immediate entry-block
fingerprint in the memo key to prevent same-name/same-shape collisions), kill
switch `SIMPLE_EXECIR=0`. Acceptance spec
`test/01_unit/compiler/interp/mir_interp_execir_tier_spec.spl` 4/4 (differential,
fallback, memo-collision, div/0 message parity), sabotage green->red->green; all
prior ExecIR/interp suites stay green (6/6, 8/8, 9/9, 11/11, 12/12).

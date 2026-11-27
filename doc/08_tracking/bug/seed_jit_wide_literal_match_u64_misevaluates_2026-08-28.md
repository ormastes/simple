# Seed JIT: literal-arm `match` on u64 mis-evaluates in a stdlib module (2026-08-28)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** fixed for the JIT (re-verified 2026-11-06, see "Re-verification 2026-11-06"); re-verified 2026-11-11 (lane interp12) on fresh seed 46fe8f6b6def — JIT and interpreter both correct, prevention spec 3/3 GREEN (see "Addendum 2026-11-11"). Workaround shipped (table scan), filed per CLAUDE.md rule
"when a compact expression form fails ... record a concrete bug".

## Symptom
Inside `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl`, a function of
the shape

```simple
fn csr_is_supported(addr: u64) -> bool:
    match addr:
        case 0xF14: true
        case 0x300: true
        ...
        case _: false
```

returned **false for every input** (including exact arm literals) when run
under `bin/simple run` / `simple test` on the Rust seed (binary: f92fa0bb4d5
tree + hal patch, `--features llvm`, 183,650,976 bytes 2026-08-28 09:03).

## What discriminates
- Identical standalone probes PASS: single- and 29-arm matches, hex vs
  decimal literals, docstring variants, half/quarter splits of the same arm
  table — all true (`build/hal_fx/probe_match.spl`, `probe_arms.spl`,
  `probe_arms2.sh/.spl` in the worktree; copies in the session scratchpad
  `hal/evidence/`).
- The same function imported from the stdlib module OR pasted locally into a
  file that imports the module returned false (`probe_sup.spl`,
  `probe_sup2.spl`) — so the trigger involves the module context (this module
  drops to JIT fallback with `jit-fallback ... rt_char_from_code`), not the
  match shape alone.
- Bisection by arm count/position inside the probe file did NOT reproduce;
  half-tables gave position-dependent false (`h1=false h2=true q3=true
  q4=false` in one run) — evaluation is unstable, not a simple wrong-arm.

## Workaround shipped
`csr_is_supported` uses a `[u64]` table + linear scan instead of `match`
(commit-pending hal intrinsics patch). The csr_read/write intrinsic matches
are unaffected in native codegen (objdump shows every arm; see
`hal/impl_B_REPORT.md`), and their host path is shim-gated before the match.

## Repro
```
build/hal_fx/seed_after run build/hal_fx/probe_sup2.spl   # false false ...
build/hal_fx/seed_after run build/hal_fx/probe_arms2.spl  # h1=false q4=false
```
(from the hal impl_B worktree; probes are also in the scratchpad copy).

## Next step
Minimise from `probe_sup2.spl` + the module import; suspect the JIT-fallback
interpreter's u64 literal comparison in imported-module context.


## Re-verification 2026-11-06

On a seed built from `origin/release/1.0.0` @ ecb705896a4 (`cargo build --release --bin simple`, Windows x86_64 host), neither the standalone shape nor the module-context shape reproduces:

- `csr_is_supported(0xF14)` / `(0x300)` imported from
  `std.nogc_async_mut_noalloc.baremetal.riscv.csr`, plus a local 6-arm
  `match addr: u64` in a file that imports that module: JIT and interpreter both
  print `lib true true` / `local true true true true false` (all correct).
- Standalone arms including `case 0x8000000000000000`: JIT
  `true true true false` (correct).

**Residual, interpreter-only (not a JIT defect, out of this lane):** the
interpreter answers `false` for `sup(0x8000000000000000)` against a
`case 0x8000000000000000` arm on a `u64` scrutinee (JIT: `true`). The literal
arm is presumably compared as a signed i64 against a `Value::UInt`. This
belongs to the seed-interpreter owner.


## Round 15 note (2026-11-07, work/r15-stdlib-20261107)

Interpreter high-bit literal arm already fixed in source (777859ac906); the stock seed binary predates it. Spec test/01_unit/lib/nogc_async_mut_noalloc/u64_literal_match_prevention_spec.spl is RED on the stale seed (arms above i64::MAX) and expected GREEN on a seed rebuilt from this tree.


Round 15 update: verified on a seed built from this tree (D:/dev/wt/target-stdlib): u64_literal_match_prevention_spec 3/3 GREEN (was RED on the stale seed).


## Addendum 2026-11-11 (lane interp12) — re-verified FIXED on fresh seed 46fe8f6b6def

**Verification actually run** (worktree simple-p3-interp12-20261111, seed-smoke):

```
# JIT lane (default run):
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe run \
  test/fixtures/seed_interp/u64_high_bit_literal_pattern_repro.spl --no-cache
# u64_high_bit sign other        (rc=0)

# interpreter lane:
SIMPLE_EXECUTION_MODE=interpret ./bin/simple.exe run \
  test/fixtures/seed_interp/u64_high_bit_literal_pattern_repro.spl --no-cache
# u64_high_bit sign other        (rc=0)

# prevention spec:
./bin/simple.exe test test/01_unit/lib/nogc_async_mut_noalloc/u64_literal_match_prevention_spec.spl \
  --mode=interpreter --no-cache
# SPEC FILE VERDICT: outcome=OK declared>=3 executed=3 passed=3 failed=0
```

The residual interpreter-only high-bit arm tracked here is fixed by
`777859ac906` (an ancestor of this seed's build commit) and is also closed by
`seed_interp_u64_high_bit_literal_pattern_2026-11-06.md` (FIXED). Verdict:
STALE (no new code change this lane).

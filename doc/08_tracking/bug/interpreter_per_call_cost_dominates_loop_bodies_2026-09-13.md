# Every loop-body shape above the generic floor is dominated by one call
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found by: PERF-6, base `origin/main` f26970e9d93, seed sha256 `22878382bc1b5ccf...`

## The corpus

12 statement shapes that dominate real stdlib loops, timed in-loop at
n = 2,000,000 under `SIMPLE_EXECUTION_MODE=interpreter`, best of three:

| shape | ns/iteration | src/lib/common sites |
|---|---:|---:|
| range `for` (`acc = acc + i`) | 96 | 39 |
| nested `for` (inner 2 stmts) | 264 | -- |
| array index read in a `for` | 1,190 | 10,859 |
| array `push` in a `for` | 1,184 | 5,774 |
| text concat | 1,049 | 1,843 |
| dict get + set | 1,456 | 721 |
| `while` with two accumulators | 1,587 | 4,111 |
| closure call | 2,199 | -- |
| method call on a class (`me` mutator) | 3,079 | 21,601 |
| `match` on an enum (+ a `pick()` call) | 4,647 | 953 |
| Option unwrap `f(i) ?? 0` | 4,982 | 167 |
| StringBuilder `push` | 7,905 | 54 |
| tuple destructure `val (a, b) = pair(i)` | 8,733 | ~0 |

## The finding

The three cheapest generic shapes -- array index read, array push, text concat
-- all sit at 1,050-1,190 ns/iteration for a two-statement body. **That is the
generic walk's floor, not a property of arrays or of text.** Arrays, dicts and
text concatenation are not distinct hot mechanisms; PERF-1 already certified
this space linear.

Everything above the floor is a *call*: the excess is ~1,000 ns for a closure,
~1,900 ns for a class method, ~3,500-3,900 ns when the shape also calls a
helper (enum match, Option unwrap). By cost x frequency the largest single
target in the interpreter is therefore **the per-call cost of a method on a
class or struct**: 3,079 ns x 21,601 sites.

`src/compiler_rust/compiler/src/interpreter_call/` carries 282 `.clone()` /
`Env::clone` sites. PERF-6 did not attempt this: it is not a contained edit, and
on this host it cannot be measured honestly without a CPU-time harness (see
`perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md`). Filed so the
next lane starts from the measurement rather than from a guess.

## Separately anomalous

`val (a, b) = pair(i)` costs **8,733 ns/iteration**. A call plus a two-name
tuple bind should be ~4,000 given the closure and method-call rows above; the
extra ~4,500 ns is unexplained and is the largest per-statement cost in the
corpus. The destructuring path is also the only block-shadow capture path that
still allocates a scratch vector.


## Addendum 2026-11-11 (lane interp6) — SUPERSEDED (measurement acted upon; pins green on refreshed seed)

**Verdict: SUPERSEDED.** This PERF-6 survey is a measurement record, not a
discrete defect; the per-call-cost campaign it filed was executed by later
lanes, and the loop/call shapes it names are pinned green on the refreshed
seed today.

Fixing lineage on origin/release/1.0.0:

- `e73a0bec647` (2026-08-21, ancestor): scope-chain `CowEnv` replaces
  per-call env clone — lint of driver_types.spl 90 s/2 GB -> ~24 s/0.5 GB.
  (Predates this survey; the survey measured the residual cost WITH CowEnv.)
- PERF-7 / PERF-9 (2026-09-13): owned-receiver call components and the
  caller-frame-width publish term — recorded fixed in
  `interpreter_owned_method_call_component_attribution_2026-09-13.md`;
  carried on this branch by squash-merge
  `9e7e7a526edb43ab29171d920449367e5fd48127` (2026-11-07, PR #7597).
- 2026-11-07 owned-call campaign: `OWNED_NS_*`/`EVALCALL_NS_*` phase counters
  (`perf_counters.rs`) plus the generation-preserving global write-through
  (`sync_flat_global`, `interpreter_helpers/patterns.rs:1127` — a
  module-global write no longer bumps the env-template generation, killing
  the 165k full rebuilds per lint the template cache used to thrash on).

**Seed-smoke verification (refreshed seed, build-commit 0791c2b7f4a7):**

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe $PWD/bin/simple.exe test \
  test/05_perf/interp/push_call_loop_env_cache_spec.spl --mode=interpreter --no-cache
  -> outcome=OK, 1 passed, 0 failed   (call-in-loop env rebuild: 2000 iters < 600 ms)

SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe $PWD/bin/simple.exe test \
  test/05_perf/interp/while_loop_shape_parity_spec.spl --mode=interpreter --no-cache
  -> outcome=OK, 7 passed, 0 failed   (`x = x + f(y)` within 3x of the fast shape)
```

Standing notes that are NOT defects and stay open as ordinary perf debt:
the `.clone()`-density observation (a current line-count of the same
patterns in `src/compiler_rust/compiler/src/interpreter_call/` is ~450, same
order as the 282 recorded — methodology differs, no target was ever pinned),
and the tuple-destructure block-shadow scratch vector
(`save_pattern_scope` in `interpreter_helpers/patterns.rs:33` still allocates
one per destructure). Neither has a correctness or budget criterion attached;
the corpus's absolute ns/iteration figures are host-and-seed-bound to the
2026-09-13 measurement and are superseded by the ratio/count pins above.

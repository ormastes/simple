# Pre-push hook is unpassable: check-native-extern-fabrication depends on native-build, which is SIGKILLed at >24 GB

**RESOLVED 2026-08-18** (verified at `ce396605fef`, pristine `origin/main`).
Status was OPEN; it is now closed by `e78c7bf3779` ("fix(desugar): break an
unbounded global-array push loop that OOMed native-build", landed 2026-08-18
08:56 -- three commits before the verification tip). This record was filed
BEFORE that commit, so its OPEN status was simply stale, not wrong.

The control fixture was never the defect and neither was the guard: plain
`native-build` genuinely could not build ANY program, the trivial control
included. The underlying fault is an interpreter defect -- on a MODULE-GLOBAL
array, `.push()` grows a live copy while `.len()` in a `while` condition still
reads the stale global, so
`transform_placeholder_call_args_after_interpolation`
(`src/compiler/10.frontend/desugar/placeholder_lambda.spl:342`) never
terminates and pushes until the worker is killed. That single loop explains
BOTH recorded shapes: the 7200s `worker timed out` in this record and the
rc=143/134 >24 GB SIGKILL in
`prepush_hook_unpassable_native_build_oom_2026-08-17.md`.

Evidence at `ce396605fef`, `bin/simple` = the shared Rust seed
(`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59546088 bytes, mtime 2026-08-18 07:53:39):

- The guard's own control invocation, run by hand, exit status captured on its
  own line (never through a pipe): `CTRL_RC=0`, binary produced, and it runs
  `stdout=[ctrl-ok] exit=7` -- exactly what the guard asserts. ~4 min wall,
  worker peak ~2.88 GB RSS, CPU/elapsed ~1:1 (compute-bound, not blocked).
- `sh scripts/check/check-native-extern-fabrication.shs --selftest` ->
  `PASS — selftest: 19 fixture assertion(s) checked, 0 failed` (exit 0).
- Full guard run -> exit 0, verdict line:
  `PASS — native-build extern fabrication: control unaffected, known-open gap unchanged`
  with no `FAIL — control fixture` line anywhere in the output.

Nothing in the guard was weakened, relaxed, or deleted to reach green; the
control fixture is untouched and still fails the gate if native-build breaks
again. The extern-fabrication gap the guard actually fences is still OPEN and
still reported as KNOWN-OPEN (nm class `T`, 3-byte defined symbol
`lane_definitely_absent_probe`, program runs to completion printing `r=0`) on
BOTH the `[default]` and `SIMPLE_NO_STUB_FALLBACK=1` `[strict]` lanes -- so
this closure is about the infrastructure outage only, not about that gap.

---


Status: RESOLVED 2026-08-18 (see note above) — was P1, blocked every push to `main`.

## Symptom

`git push` is refused by `.git/hooks/pre-push`:

```
pre-push: BLOCKED by check-native-extern-fabrication.shs (status 1) for range
          native-build extern-fabrication probe (full scan, not range-bound)
```

Running the guard standalone (`sh scripts/check/check-native-extern-fabrication.shs`,
exit 1) gives three FAIL lines:

```
FAIL — control fixture (no extern) no longer builds under native-build
FAIL — [default] native-build exited 143, but the log never
       failure, not the expected extern-fabrication refusal. Investigate
FAIL — [strict] native-build exited 143, ...
```

## Root cause — not extern fabrication

Exit **143 is SIGTERM**: the RSS monitor killing the native-build worker. The
guard is behaving *correctly* — it refuses to infer the expected
extern-fabrication refusal from a build that died for an unrelated reason, and
says so instead of passing vacuously. It is a victim, not the defect.

The underlying defect is the native-build worker's memory blowup, measured this
session:

- The worker is the entire compiler running **interpreted**
  (`bin/simple run src/app/cli/native_build_worker.spl`).
- RSS climbs monotonically through `parse`: **3.7 → 3.9 GiB in 20 s** on a
  one-module, no-import fixture.
- On a 20-line fixture it was killed by `kill_simple_monitor` at
  **rss=24159MB ≥ 24000MB**, still loading `src/compiler/20.hir/**`, having
  emitted 0 `unresolved name` lines and produced no binary.
- Concurrent workers from other lanes were observed at 15–17 GiB.

Related records:
- `native_build_source_closure_zero_sources_2026-08-17.md` — the allocation
  abort was being **misreported as a 7200 s timeout**; fixed in
  `src/app/cli/native_build_main.spl` so the real cause is now named.
- `native_trailing_default_param_guard_*` — same blocker, same exit 143.
- `stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md` — fix
  applied but UNVERIFIABLE for this reason.

## Measured characterisation (2026-08-18)

Fixture: a 3-line `fn main() -> i64: print "hi"; 0`. Command, per mode:

```
(ulimit -v 27000000; SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=<mode> \
  timeout 600 /usr/bin/time -v bin/simple run src/app/cli/native_build_worker.spl \
  --entry tiny.spl -o tiny.bin)
```

| mode | peak RSS | wall | outcome |
|---|---|---|---|
| interpret | 12,577,548 KB (12.58 GB) | 4:45.49 | RC=134 abort, no binary |
| jit | 12,523,856 KB (12.52 GB) | 6:54.43 | RC=134 abort, no binary |

Five findings that redirect the investigation:

1. **The cost is engine-independent.** Both modes die within 0.5 % of the same
   ceiling, at the same phase (`[build] parse 0/1 step 1/6`). JIT is ~45 %
   *slower*. **Switching the default away from `interpret` does not fix this**
   — that theory is dead, and `native_build_main.spl:272` should not be
   changed on the hope that it does.
2. **The cost is fixed, not input-scaled.** A 3-line program pays 12.5 GB.
3. **Source discovery is innocent.** The build log shows `source_closure 1/1`
   for an `--entry` build; it is not scanning the tree, contrary to what
   several older records assumed.
4. **Nothing is loaded twice.** With `SIMPLE_LOADER_TRACE=1`: `resolve: 3579`,
   `cache-hit: 2663`, `loaded: 737`, `circular: 179`, 814 distinct modules —
   and **zero** paths appear more than once in the `loaded:` lines. The module
   cache works. This is not redundant work.
5. **It is a RETENTION defect.** 737 modules loaded exactly once against a
   12.5 GB peak is roughly **17 MB retained per module**, against on-disk
   sizes in the tens of KB (`hir_types.spl` 42 KB, `mir_data.spl` 40 KB) —
   about a **400x source-to-memory blowup**.

### Retention attribution (instrumented, 500 module loads)

A `TrackingAlloc` wrapper with nesting-aware **exclusive** per-module
attribution (`compiler/src/mem_trace.rs`, `SIMPLE_MEM_TRACE=1`, reports
incrementally and survives an abort) gives:

| | value |
|---|---|
| source read | 9.2 MB, 13,127 AST items |
| parse retained | 334 MB (36 bytes per source byte) |
| **eval retained** | **1150 MB (3.4x parse)** |
| env entries | 585,182 (~1170 per module) |
| export entries | 579,966 (~1160 per module) |

Growth is **linear** at ~4 MB per module load (100 -> 872 MB, 300 -> 1297 MB,
500 -> 1933 MB, 600 -> 2445 MB).

**Cost correlates with ENV WIDTH, not source size** — modules re-export their
transitive imports, so tiny files own huge maps: `codegen_factory.spl` is
3.4 KB / 20 AST items with env=5183 and retains **17.6 MB**, while
`zca_rows.spl` is 132 KB of source but env=163 and retains only 4 MB.

### One mechanism found and fixed — and honestly, it is small

`interpreter_module/module_evaluator.rs` materialised each module's visible-name
map **twice** and retained both: `filtered_env.freeze()` (held by
`MODULE_ENV_BY_OWNER`) plus `export_functions`' `Arc::new(filtered_env.clone())`
(held by every exported `Value::Function`'s `captured_env`). The clone was a
full copy because `filtered_env` is `.collect()`ed, so every entry sits in the
CoW **overlay**, defeating the O(1) Arc-base clone `CowEnv` is designed for.
Fixed by freezing once and sharing the `Arc`.

**Measured effect: eval_retained 1150.2 -> 1067.4 MB — 82.8 MB, -7.2% of eval,
-4.3% of total live.** Not the 2x that the raw 2.3 KB/entry figure suggested.

**Correction to the earlier inference in this record:** one full env copy costs
82.8 MB / 585k entries ~= **145 bytes/entry**, a plausible single copy. The
observed ~2.3 KB/entry is therefore roughly **16 copies' worth**, not 2. The
double-copy was real and is removed, but **~2.1 KB/entry of retention remains
unexplained** and is where the 12.5 GB actually lives.

Ruled out by measurement, so nobody re-investigates them:
- the four `module_cache.rs` caches (exports/classes/functions/enums) —
  1046 / 7050 / 272 total entries, and an exports hit is an `Arc` refcount
  bump, not a deep clone;
- `PARTIAL_MODULE_EXPORTS_CACHE` — hovers at 10-14 live entries and is
  correctly cleared on completion, so the circular-import lead is dead;
- garbage collection generally — there is no GC and no eviction, and nothing
  is *garbage*: every entry stays reachable by name. RSS is monotonic
  (68 samples, only 2 dips of ~2%, glibc trim noise). **The lever is loading
  fewer modules, not collecting more.**

Open candidates for the remaining ~2.1 KB/entry: `record_owned_global` storing
every global **three** times (`MODULE_GLOBALS` + `MODULE_GLOBALS_BY_OWNER` +
`MODULE_GLOBALS_INITIAL_BY_OWNER`), and `captured_env_with_live_globals`
calling `captured_env.to_map()` per call.

## THERE ARE TWO DEFECTS HERE, NOT ONE (2026-08-18)

Measured on the post-env-fix binary, 3-line fixture, external `/proc` VmRSS
sampler (note `/usr/bin/time -v` FAILS under `ulimit -v`: rc=144, no
Maximum-resident line):

```
peak_rss = 10,877 MB
rc = 134
  [build] parse 0/1 step 1/6 <fixture>
  memory allocation of 17179869184 bytes failed
  timeout: the monitored command dumped core
```

**17,179,869,184 = exactly 16 GiB = 2^34**, requested while the process held
only ~10.9 GB. That is not accumulation reaching a ceiling — **something
computes an absurd capacity in a single step**. With the 8 GiB (2^33) and
2 GiB (2^31) failures already on record, the ladder is exactly 3 bits apart.

Separate the two defects; they need different fixes:

1. **Retention** (~12 GB, proportional to env width). Makes the build fat and
   slow. The env double-copy fix addressed 4.3% of it; the rest is open.
2. **A single 16 GiB allocation request.** *This* is what aborts the build.
   No amount of retention work fixes it.

Leading hypothesis for (2), consistent with the power-of-two ladder and with
this repo's documented history of tagged integers consumed undecoded (raw
tagged words, heap pointers leaking as values, `from_int` shifting
unconditionally in `runtime/src/value/core.rs`): **a tagged count used raw as
an element count.** A tag shift of 3 bits turns a plausible N into 8N, and an
8-byte-per-element `Vec` then requests 8x again.

Next step that would end this quickly: an allocation guard that reports any
single request over ~256 MB together with the enclosing module/phase, then run
to the abort. One capture of that call site identifies the defect. The failure
occurs during `parse` of the compiler's OWN module graph, before the user
fixture is parsed.

### Secondary defect found while measuring

`SIMPLE_LOADER_TRACE=1` prints its summary only from `clear_module_cache()`,
which never runs when the process aborts — so the telemetry produces **no
summary in exactly the OOM case it exists to diagnose**. The per-line trace
still survives and is what the counts above were derived from.

## Impact

`origin/main` is in a state where its own pre-push hook cannot pass. Any lane
that pushes must either fix native-build's memory use or override the hook.

## Override taken for the 1.0.0-RC release (recorded, not hidden)

The 1.0.0-RC release commit was pushed with `--no-verify`, with explicit user
authorization, after independently validating the tree:

| check | verdict |
|---|---|
| check-no-conflict-tree-push | PASS — 1 commit, 0 conflict trees |
| check-no-conflict-markers-push | PASS — 50 files scanned, 0 markers |
| check-tree-size-push | PASS — base 115562 files, 0 structural faults |
| check-runtime-api-regression-push | PASS — 2795 symbols, 0 removed |
| check-seed-builds-push | PASS — 50 files, compiles cleanly |
| check-c-runtime-compiles-push | PASS — 106 files, 0 errors |
| check-test-tree-divergence-delta | PASS — 71 pre-existing, 0 introduced |
| **check-native-extern-fabrication** | **FAIL — native-build SIGTERM at 24 GB** |

The released diff is provably version-only (0 non-version lines) and
`cargo check --release --bin simple` is clean at that tree, so the override
carries no unvalidated content — the blocked guard could not have assessed it
either way, since native-build never ran.

## Exit criteria

1. The native-build worker builds a 20-line fixture inside a sane RSS budget.
2. `check-native-extern-fabrication.shs` reaches a real PASS or a real
   extern-fabrication FAIL — never exit 143.
3. Pushing `main` no longer needs `--no-verify`.

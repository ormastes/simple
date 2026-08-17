# Sweep: how many specs pass vacuously because of the JIT enum-associated-fn hijack?

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

- **Date:** 2026-07-28
- **Kind:** measurement (no specs were rewritten)
- **Parent bug:** `doc/08_tracking/bug/enum_associated_fn_never_called_on_jit_2026-07-28.md`
- **Artifacts:** `build/enum_vacuous_sweep/` (tool, raw TSVs, every captured run log)

## Headline

**The defect is real and slightly worse than documented, but it does not make the
spec suite vacuous.** `bin/simple test` forces interpreter execution for every
spec, and the interpreter does not have the hijack. Measured, not assumed: the
decisive mutation experiment below turned a green spec red exactly as a
non-vacuous spec should.

Two numbers:

| | count |
|---|---|
| `EnumName.assoc_fn(...)` call sites in owned `src/**` + `test/**` (upper bound) | **3,867** in 535 files |
| same, after dropping receiver names that are also declared as a class/struct/trait (lower bound) | **501** in 99 files |
| of the lower bound, call sites inside `*_spec.spl` | **363** across 50 spec files (27 after removing the duplicated legacy test trees) |
| specs sampled and re-run under mutation | 13 |
| specs found VACUOUS | **0** (8 GENUINE, 5 UNMEASURED) |

The real cost is not vacuity, it is blindness: because the runner is
interpreter-only, **no spec anywhere in the suite exercises the JIT**, so this
bug — and any other JIT regression — cannot be caught by the test suite at all.
See §6 and the corroborating lane.

## 1. The defect, re-measured

The parent bug says an *undefined* `EnumName.method()` is fabricated. It is
broader than that: a **defined** `static fn` on an enum is equally never called.

`build/enum_vacuous_sweep/probe_defined.spl`, run with `bin/simple run`
(default engine, JIT):

```
direct     = A          # EnumName.Variant       -> correct
directb    = B(7)       # EnumName.Variant(x)    -> correct
viastatic  = UNMATCHED  # EnumName.make_a()      -> matches NO case arm
viastaticb = UNMATCHED  # EnumName.make_b(7)     -> matches NO case arm
undef      = UNMATCHED  # EnumName.no_such_fn()  -> no error, exit 0
```

exit 0. So the population is not "undefined statics" — it is **every**
`EnumName.assoc_fn(...)` call site.

## 2. Why the spec suite is nonetheless not vacuous

`src/app/test_runner_new/test_runner_single.spl:328-329` (and the mirrored
`src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:164-165`) hard-set the
engine in the child process that actually executes a spec:

```
rt_env_set("SIMPLE_RUNTIME_MODE", "interpreter")
rt_env_set("SIMPLE_EXECUTION_MODE", "interpret")
```

It is unconditional — the parent's `options.mode` does not reach it. Every spec
therefore runs on the interpreter, which the parent bug already records as
**correct** on this construct (it raises `unknown variant or method` instead of
fabricating a value).

This is exactly the `bin/simple run` vs `bin/simple test` divergence the task
warned about, and here it is load-bearing: **the defect is a `bin/simple run` /
JIT defect, not a spec-suite defect.**

## 3. How the population was counted

Tool: `build/enum_vacuous_sweep/sweep.spl` (pure Simple, ~250 lines).

- **Input list** from `git ls-files` restricted to tracked `.spl` under `src/**`
  and `test/**`, minus `src/compiler_rust/vendor/**` and `src/runtime/vendor/**`
  → 33,072 files, 9.5 MB. A directory walk was tried first and abandoned: the
  tree holds 63 symlinks (`src/std -> lib`, 17 `src/compiler/<alias> -> NN.<name>`,
  and recursive ones such as `test/feature/lib/lib`), which both double-count and
  fail to terminate.
- **Pass 1** records every `enum` declaration with (a) its VARIANT list — body
  lines at the exact variant indent whose first character is uppercase, stopped
  at the first `fn`/`static fn` at that indent, plus the inline `enum X: A, B`
  form — and (b) its `static fn` list. Result: 2,507 declaration sites, 1,493
  distinct enum names. It also records every `class`/`struct`/`trait`/`type`/
  `actor`/`mixin` name (13,080) for the disambiguation step below.
- **Pass 2** splits each line on `.` and flags `Recv.member(` where `Recv` is a
  declared enum name and `member` is **not in that enum's variant list**. This is
  how a variant construction is told apart from an associated-function call — the
  actual parsed variant list, not capitalisation. For calibration: 29,073
  variant constructions were correctly recognised and excluded, and the
  capitalisation heuristic alone would have misclassified hundreds of them.

### Upper vs lower bound, and why both are reported

The raw result is **3,867** call sites. Inspecting it showed two false-positive
families:

1. **Receiver-name collisions.** `Shape.new` (599 hits), `Value.int`, `List.new`,
   `Point.create`, `Environment.new` — these are *class* statics that happen to
   share a name with an enum declared in some other module. A whole-repo name
   table cannot resolve which one a given file imported.
2. **Truncated variant lists.** Large enums (`Node`, `Expr`, `Value`,
   `InterpreterError`) whose bodies the indent heuristic did not fully consume,
   leaving real variant constructions (`Expr.Bool(`, `Node.Const(`) looking like
   associated calls. Every one of these has an **uppercase** member.

The lower bound **501** drops both families: receiver must not be declared as a
class/struct/trait anywhere, and member must start lowercase. This is
conservative in the other direction — it wrongly drops `SdnValue.*` (351 hits),
because two unrelated compiler modules declare a `struct SdnValue`
(`src/compiler/70.backend/backend_types.spl:133`,
`src/compiler/80.driver/init.spl:280`). The true figure sits between the two.

Known limitations, stated rather than hidden: string literals and block comments
are not excluded; 88 fully-qualified `mod.Enum.fn(` calls are counted separately
and excluded; and an enum-body `fn` with no `self` (e.g.
`ReplayEventKind.from_i32` at `src/lib/nogc_sync_mut/replay/core/replay_event.spl:31`)
is reported as `UNDEFINED` although it is really an associated function.

## 4. Specs reached

50 spec files contain a lower-bound call site; 27 after removing the duplicated
legacy trees (`test/unit/**`, `test/system/**` mirror `test/01_unit/**`,
`test/03_system/**`). Full table in
`build/enum_vacuous_sweep/affected_specs_clean.tsv`.

The 27, by call-site count:

| spec | sites |
|---|---|
| `src/compiler/70.backend/linker/test/smf_enums_spec.spl` | 34 |
| `test/01_unit/compiler/config/chained_enum_method_spec.spl` | 33 |
| `test/01_unit/compiler/config/type_inference_config_spec.spl` | 25 |
| `test/03_system/tools/replay_core_spec.spl` | 12 |
| `test/01_unit/compiler/config/compiler_profile_spec.spl` | 12 |
| `test/03_system/tools/replay_feature_registry_spec.spl` | 9 |
| `test/03_system/tools/replay_process_e2e_spec.spl` | 8 |
| `test/03_system/tools/replay_divergence_spec.spl` | 8 |
| `test/03_system/compiler/severity_spec.spl` | 8 |
| `test/03_system/tools/replay_qemu_e2e_spec.spl` | 6 |
| `test/03_system/tools/replay_semantic_trace_spec.spl` | 5 |
| `test/03_system/tools/replay_qemu_arch_spec.spl` | 5 |
| `test/03_system/tools/replay_kernel_event_spec.spl` | 5 |
| `test/shared/control_flow/static_fn_spec.spl` | 4 |
| `test/03_system/tools/replay_thread_chaos_spec.spl` | 4 |
| `test/03_system/compiler/mir_types_spec.spl` | 4 |
| `src/compiler/70.backend/linker/test/smf_integration_spec.spl` | 4 |
| `src/app/interpreter/async_runtime/actor_scheduler_spec.spl` | 4 |
| `test/03_system/tools/replay_event_log_spec.spl` | 3 |
| `test/01_unit/lib/package/installer/installer_spec.spl` | 3 |
| `test/03_system/tools/replay_semantic_event_spec.spl` | 2 |
| `test/03_system/check/gui_widget_rendering_fixture_coverage_spec.spl` | 2 |
| `test/03_system/tools/replay_process_rr_spec.spl` | 1 |
| `test/01_unit/lib/{nogc_async_mut,gc_async_mut}/replay/core/replay_core_facade_spec.spl` | 1 each |
| `test/01_unit/lib/{nogc_async_mut,gc_async_mut}/replay/adapters/replay_adapters_facade_spec.spl` | 1 each |

The upper bound reaches 244 spec files (158 after removing duplicated trees); its
extra members are dominated by the two false-positive families above plus the
`SdnValue.*` family, which the sample covers directly.

## 5. The decisive experiment

For each sampled spec the **declaration** of the enum associated function it
depends on was renamed (`from_text` → `zzz_from_text`, etc.) while every call
site was left untouched. Class statics in the same files were deliberately left
alone as a control. Under a correct engine the call no longer resolves and the
spec must fail; under the JIT hijack it would silently keep passing. A spec that
stays green is vacuous.

Mutation script: `build/enum_vacuous_sweep/mutate.shs`. Runner:
`build/enum_vacuous_sweep/run_sample.shs` (strictly sequential — parallel runs
corrupt the shared test DB). Every run captured to a file and read from the
TAIL; every `N examples, M failures` line per describe block was collected, not
just the first.

Mutated declarations (25 in 8 files): `SdnValue.{null,bool,int,float,string,array,empty_array,empty_dict}`,
`CompilerProfile.from_text`, `TypeDefault.from_text`, `ReplayEventKind.from_i32`,
`Arch.from_text` (replay), `Severity.{reset_color,from_name,all}`,
`{Platform,Arch,CompressionType,SmfAppType}.from_u8` (SMF),
`InstallerPlatform.{all,from_string}`, `Direction.{northeast,southeast,southwest,northwest}`.

All runs `bin/simple test`, sequential, each captured to
`build/enum_vacuous_sweep/{base,mut}/`. Both engines were exercised on the
construct itself (`bin/simple run` for the probe, `bin/simple test` for the
specs) and they disagree — that disagreement is the whole finding.

| # | spec | baseline | with subject broken | verdict |
|---|---|---|---|---|
| 1 | `test/01_unit/lib/common/sdn_coverage_spec.spl` | 51 ex / **1** fail | 51 ex / **50** fail | **GENUINE** |
| 2 | `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl` | 51 ex / **1** fail | 51 ex / **50** fail | **GENUINE** |
| 3 | `test/01_unit/lib/gc_async_mut/dl/config_loader_spec.spl` | exit 0, **no `N examples` line at all** | identical | **UNMEASURED** |
| 4 | `test/01_unit/compiler/config/chained_enum_method_spec.spl` | 22/0, 7/0, 2/0 | 22/**22**, 7/**6**, 2/**1** | **GENUINE** |
| 5 | `test/01_unit/compiler/config/type_inference_config_spec.spl` | 40/25, 23/**0** | 40/25, 23/**11** | **GENUINE** |
| 6 | `test/01_unit/compiler/config/compiler_profile_spec.spl` | 16/0 | 16/**12** | **GENUINE** |
| 7 | `test/03_system/tools/replay_core_spec.spl` | 12/0, 5/0, 7/0, 4/0, 2/0 | 12/**12**, rest unchanged | **GENUINE** |
| 8 | `test/03_system/tools/replay_feature_registry_spec.spl` | 8/0, 2/0, 2/0 | identical | **UNMEASURED** — subject is `FeatureId.from_i32` in `src/app/debug/remote/feature/features.spl`, not among the mutated files |
| 9 | `test/03_system/tools/replay_divergence_spec.spl` | 8/0, 4/0, 2/0, 2/0, 3/0, 2/0, 3/0 | identical | **UNMEASURED** — subject is `DivergenceKind.from_i32` in `src/os/kernel/replay/divergence.spl`, not mutated |
| 10 | `test/03_system/compiler/severity_spec.spl` | 23/0 | 23/**8** | **GENUINE** |
| 11 | `test/shared/control_flow/static_fn_spec.spl` | 14/**4** | 14/4 (identical) | **ALREADY RED, not vacuous** — see below |
| 12 | `src/compiler/70.backend/linker/test/smf_enums_spec.spl` | 5/0, 7/0, 5/0, 5/0 | 5/**3**, 7/**3**, 5/**3**, 5/**3** | **GENUINE** |
| 13 | `test/01_unit/lib/package/installer/installer_spec.spl` | 7/7, 2/2, 5/5, 2/2 — **fully red already** | identical | **UNMEASURED** (pre-existing failure, nothing left to break) |

**8 GENUINE, 0 VACUOUS, 5 UNMEASURED.**

Every GENUINE verdict is backed by the same diagnostic — the exact error the JIT
suppresses:

```
✗ parses dev
  semantic: unknown variant or method 'from_text' on enum CompilerProfile
✗ FunctionEnter to_i32 round-trip
  semantic: unknown variant or method 'from_i32' on enum ReplayEventKind
✗ converts from u8 to Platform correctly
  semantic: unknown variant or method 'from_u8' on enum Platform
✗ gets reset color code
  semantic: unknown variant or method 'reset_color' on enum Severity
```

### Row 11 is worth reading closely

`static_fn_spec.spl` did not change under mutation because its four
`Direction.*` examples were **already failing at baseline**, with:

```
Direction factory methods
  ✗ creates northeast direction
    semantic: unknown variant or method 'northeast' on enum Direction
```

So an enum `static fn` declared **inside a spec file** does not resolve even on
the interpreter, while the same construct in a library module
(`SdnValue.int`, `Severity.from_name`) resolves fine. That is a separate,
already-visible gap — the spec is honestly red about it, which is the opposite
of vacuous. It also explains why a first attempt at a self-contained guard spec
(`build/enum_vacuous_sweep/enum_static_guard_spec.spl`) failed all four
examples including plain variant construction: a locally declared enum in a spec
file is not a usable control here.

## 6. Where the exposure actually is

The hijack is untouched by any of this — it is only the *spec suite* that is
insulated, because of one hard-coded env var. Real remaining exposure:

- **49 non-spec source files** carry lower-bound call sites, including the
  compiler itself: `src/compiler/35.semantics/semantics/binary_ops.spl` (13),
  `src/compiler/80.driver/main.spl` (6), `src/compiler/00.common/config.spl` (6),
  `src/compiler/30.types/bidirectional_checking.spl` (6). Anything built or run
  through the JIT/native path exercises those with fabricated values.
- Any evidence produced by `bin/simple run ...` (rather than `bin/simple test`)
  is on the defective engine and is **not** covered by this sweep's negative
  result.
- `bin/simple` on this machine still prints the bootstrap-seed banner
  (`bin/release/x86_64-unknown-linux-gnu/simple`, built 2026-07-27 22:06), so all
  results here are seed results.

### Corroboration from a parallel lane

While this sweep was running, another lane landed the same engine split
independently and much more broadly:
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`, now
summarised in `.claude/rules/testing.md`. Its finding — `bin/simple run` is
Cranelift JIT, `bin/simple test` is the tree-walk interpreter, and
`TestExecutionMode` has **no JIT variant at all**, so the spec suite *cannot*
reach the engine ordinary programs run on — is exactly the mechanism measured
here, arrived at from the opposite direction (divergent builtins rather than
enum statics). Treat the two as one result.

That lane's framing is the sharper one for this bug: the specs are not lying
about what they test, but they are **structurally incapable of catching a JIT
regression**, this one included.

## 7. Recommendation

Do not rewrite specs — none of the 13 sampled is vacuous, and rewriting them
would be work aimed at a defect they do not have.

1. Fix the parent bug's step 1: make the JIT's `func_ids` miss an **error**
   rather than a silent fall-through. The spec suite will not notice, because it
   never used that path — which is precisely the problem.
2. The structural fix is a JIT lane for the spec runner (`TestExecutionMode` has
   no JIT variant). Until that exists, no amount of green spec output is evidence
   about the JIT, and this bug will keep being discoverable only by hand.
3. Re-audit evidence produced through `bin/simple run` from the 49 affected
   non-spec source files.

## Method notes / caveats

- Runs were strictly sequential, but **other sessions were running
  `bin/simple test` concurrently on this machine** throughout (observed:
  `borrow_check_spec`, `executable_size_spec`, `with_lock_guard_spec`,
  `build/probe_divergence/*`). The shared test DB was therefore not exclusively
  ours. Verdicts here rest on per-run captured stdout, not on the DB, so this
  affects timing rather than correctness — but it is not a clean-room result.
- Every `N examples, M failures` line was collected per describe block, and the
  file TAIL was read, never `| head`.
- `bin/simple` still prints the bootstrap-seed banner; one spec was observed
  executing via `src/compiler_rust/target/debug/simple`. These are seed results.
- All eight mutated files were restored from backups taken at lane start and
  verified byte-identical with `diff`; no `zzz_` marker remains in `src/**` or
  `test/**` beyond three pre-existing unrelated hits in
  `aop_ordering_spec.spl`. The restore window was ~40 minutes, so a parallel
  edit to one of those eight files during the window could have been overwritten;
  the two files that are `M` in the working tree (`src/lib/common/sdn/value.spl`,
  `src/compiler/00.common/config.spl`) were re-inspected afterwards and still
  carry the parallel session's Dict-pitfall fixes, not mutation text.

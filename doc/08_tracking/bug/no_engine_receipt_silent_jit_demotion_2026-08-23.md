# No engine receipt: every "same on both engines" claim was unfalsifiable (2026-08-23)

**Status:** FIXED (receipt landed; the demotions it exposes remain open, by design —
this change makes them visible, it does not remove them).

## The defect

`bin/simple run` printed nothing that said which engine executed the program.
Combined with whole-module silent demotion, that made a whole class of claims
unverifiable rather than merely unverified.

`doc/01_research/compiler/dual_impl_test_sharing_assessment_2026-08-23.md`
(landed `29bea87de9e`) ran one spec, 220 lines, 39 examples, under both `run`
lanes:

| invocation | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret bin/simple run <spec>` | `39 examples, 0 failures`, rc=0 |
| `SIMPLE_EXECUTION_MODE=jit bin/simple run <spec>` | `39 examples, 0 failures`, rc=0 |

and had to label the identical rows unusable, because they are equally
consistent with the JIT genuinely running the spec and with the JIT having
silently degraded to the interpreter. That assessment's own recommendation #2
was "print an engine receipt on every run", and this is it.

Three facts made the hazard structural rather than incidental:

1. **One construct demotes the WHOLE program.** There is no per-function
   JIT/interpreter split on the `run` path. When
   `exec_core.rs::interpreter_preference_reason` fires, `run_file_jit` is never
   called and nothing is JIT-compiled at all.
2. **The gates test SOURCE TEXT, not semantics.** `window_winit`, `std.cli`,
   `get_cli_args`, `sys_get_args`, `rt_get_args` are substring-matched against
   the entry file. This is not a hypothetical: while writing the fixtures for
   this fix, `jit_clean.spl` de-JIT'd **itself** because an early draft of its
   own explanatory comment listed the tokens it was avoiding. The receipt
   caught it on the first run. That is the defect demonstrated on the fix's own
   test data.
3. **`SIMPLE_NO_JIT=1` is a decoy.** Zero readers in `src/compiler_rust`. Any
   A/B done with it compared JIT against JIT.

## The fix

`src/compiler_rust/common/src/engine_receipt.rs` — a small non-forgeable record.

**Receipt format** (stderr, one line, stable, opt-in via `SIMPLE_ENGINE_RECEIPT=1`):

```
[engine-receipt] engine=<E> requested=<R> demoted=<yes|no> reason=<R|-> file=<PATH>
```

`engine` ∈ `interpreter | cranelift-jit | llvm-jit | native | wasm | unstamped`.

**Demotion announcement** (stderr, always, no knob):

```
[engine-demotion] reason=<TOKEN> detail=<TEXT>
```

### Why it cannot be forged

* `Engine` is a closed Rust enum, not a string. There is no public setter
  taking an engine name from outside, so no flag and no env var can put a value
  in the field.
* `stamp()` is called from **inside each engine's own execution entry**, never
  from the CLI layer that requested a lane:
  * `compiler/src/interpreter/public_api.rs`
    `evaluate_module_with_di_and_aop` — the tree-walk entry every demotion path
    converges on;
  * `compiler/src/codegen/local_execution.rs` `execute` — on the branch about
    to jump into machine code, per backend;
  * `driver/src/exec_core.rs` `execute_and_gc` — the loaded-SMF lane.
* Last writer wins, deliberately: when the JIT gives up, the interpreter stamps
  itself afterwards, so the field always names the engine that really ran.

### Why the demotion signal is not suppressible

`record_demotion` announces on stderr whenever the run would otherwise have
executed compiled code, with no env var that disables it, and it does so
*before* the `SIMPLE_JIT_COVERAGE` gate in `jit_coverage_report` rather than
inside it — the census is a debugging convenience and may stay off; the record
may not.

**An unset `SIMPLE_EXECUTION_MODE` counts as requesting a compiled lane.** This
is the load-bearing detail and an earlier draft got it backwards. The seed's
default lane already IS the JIT, so scoping the announcement to an *explicit*
request would have left the single most common demotion path — a default-lane
run quietly dropping to the interpreter — exactly as silent as before. Only an
explicit `interpret`/`wasm` request silences it, and there the interpreter is
what was asked for, so there is nothing to announce. The test runner forces
`SIMPLE_EXECUTION_MODE=interpret` on its `run` children, so the 21,208-file
suite gains no new stderr output from this change.

## Class sweep — every demotion point now recorded

| site | reason token | previously |
|---|---|---|
| `exec_core.rs` forced-source allowlist | `forced-source-allowlist` | silent unless `SIMPLE_JIT_COVERAGE=1` |
| `.shs` extension | `shs-extension` | same |
| unbacked argv runtime | `cli-args-unbacked-runtime` | same |
| `window_winit` source text | `jit-unsafe-graphics` | same |
| JIT compile failure (covers every `codegen/jit.rs` bail: unsupported lambda, named-fn-as-value, unresolved import) | `jit-compile-error` + the real message | `[INFO]` line only |
| JIT panic | `jit-panic` + payload | `[INFO]` line only |
| no `fn main` → module handed to the interpreter inside `run_file_jit` | `jit-bail:no-main-fn` | fully silent |
| unresolvable externs spliced back to the interpreter per call | `hybrid-interp-splice` + symbol list | fully silent |

The last two were not covered by any existing diagnostic. `hybrid-interp-splice`
is a PARTIAL demotion — the rest of the module stays JIT'd, so the engine field
still reads `cranelift-jit` — but an unqualified "ran on the JIT" would
overstate it, so it is named.

**Not covered, and why:** `src/app/io/jit_ffi.spl:283`
(`jit_native_available()` logging "Native JIT unavailable: using in-process
CompilerDriver") is on the PURE-SIMPLE side and is not a demotion at all — it
is a hardcoded `false`, a permanent state rather than a runtime fallback. It
needs a receipt of its own when the pure-Simple compiler becomes a real
execution lane; recorded here so the negative is not re-investigated.

## Evidence

`scripts/check/check-engine-receipt-discriminates.shs` — fail-closed, verdict on
the last stdout line, fatal 8-fixture `--selftest`, ERROR (never PASS) on a
missing binary or a zero-assertion run.

Its central assertion is that the two halves of the pair must DIFFER. A guard
that only checked "a receipt was printed" would go green on a receipt hardcoded
to `jit`, which is the failure mode being fixed.

**Pre-fix, against the deployed seed:** `FAIL — 2 assertion(s) checked`,
`no [engine-receipt] line for .../jit_clean.spl (pre-fix state: no receipt is
emitted anywhere)`.

## The discriminating pair

`test/fixtures/engine_receipt/jit_clean.spl` — arithmetic and `print`, no
imports, none of the trigger tokens anywhere including comments.

`test/fixtures/engine_receipt/demote_graphics_text.spl` — one string literal
containing `window_winit`. Nothing in it touches graphics. It runs, exits 0, and
its stdout is indistinguishable from a JIT run. Only the receipt separates them.

`d.insert(...)`, which `.claude/rules/testing.md` also lists, was tried first
and rejected as a fixture: on this seed it does not demote, it hard-errors
(`Function 'insert' not found`). A fixture that fails loudly proves nothing
about a defect whose entire nature is that it is quiet.

# The paired-timing spec is blocked by interpreted SHA-256, not by its accumulator

**Status:** OPEN — the spec still times out
**Found:** 2026-08-05
**Component:** `src/lib/common/crypto/x25519_mlkem768/qualified_timing.spl`,
`src/app/test_runner_new/test_runner_single.spl`
**Impact:** `x25519mlkem768_qualified_timing_spec.spl` has never produced a real
9-example verdict.

## The prior diagnosis was wrong

It was recorded that `_sample_set_material` built its digest input with
`material = material + …` in a loop, making it quadratic, and that this was why
the spec never finished. Measured cost split at n=1025 samples:

| component | time | share |
|---|---|---|
| concat accumulator | 0.35 s | ~0.3% |
| join-once replacement | 0.51 s | — |
| **`sha256_text`** | **102.3 s** | **99.7%** |

The accumulator was never the bottleneck. **Interpreted `sha256_text` is**, and
it is *linear*, not quadratic: 721 B → 3.49 s, 25,553 B → 102.3 s, i.e. roughly
**4 ms per byte**.

## The engine, and why the fix does not help today

`bin/simple test` **hard-forces the interpreter**:

```
src/app/test_runner_new/test_runner_single.spl:628-629
    rt_env_set("SIMPLE_RUNTIME_MODE", "interpreter")
    rt_env_set("SIMPLE_EXECUTION_MODE", "interpret")
```

Measured on that engine, join-once is **~4% SLOWER** than concat at n=30
(119.7/117.9 ms vs 115.3/113.7 ms) and inconclusive at n=1025. Under the JIT the
same change is **4x faster** (164 ms → 40 ms) — but the spec suite can never
reach the JIT. So the change is asymptotically correct and helps only on an
engine this spec cannot run on.

It is landed anyway because it is proven bit-identical and strictly better in
complexity, **not** because it fixes anything measurable today.

## Bit-identity — proven, not assumed

The digest input is netstring framing,
`_timing_frame(k,v)` = `<len(k)>:<k>=<len(v)>:<v>;`, concatenated with no
separator. Digests captured before the edit and recomputed after are identical
at every size tested: n = 0, 1, 2, 7, 30, 64, 129, 1025 (e.g. n=30 →
`413ef6c9…732367`, n=1025 → `bf955606…ce9980`). The second hunk was proven
separately at n = 0/1/33/257. Any change to these bytes would silently invalidate
every pinned receipt in the campaign.

## A fourth timeout ceiling

`src/app/test_runner_new/test_runner_single.spl:129` — `var timeout_secs = 120`.
The child runner's default is **120 s**, and `SIMPLE_TIMEOUT_SECONDS=0` does not
lift it. The campaign now has four distinct limits, each with its own symptom:

| limit | where | symptom | liftable |
|---|---|---|---|
| ~60 s CPU guard | resource monitor | exit 143 at ~62 s | `SIMPLE_TIMEOUT_SECONDS=0` |
| **120 s child default** | `test_runner_single.spl:129` | timeout at 120 s | `--timeout` |
| 600 s daemon cap | `test_daemon/light_protocol.spl:1-2` | `test daemon timed out` | no — run detached |
| 10M operations | interpreter | aborts, **no verdict line** | `rt_fault_set_execution_limit(0)` |

## Reading the verdict line correctly

The timed-out run reports:

```
Process timed out
Results: 1 total, 0 passed, 1 failed
Duration: 2400026ms
```

That `1 total` is the **file-level wrapper** counting the spec file as one
timed-out unit. It is **not** the 9 `it` blocks, and must not be read as "1
example ran". Even at a 2400 s budget the spec consumed the whole thing.

## Why it cannot pass yet

The 1025-sample example alone needs ~300 s of interpreted hashing: the material
is hashed at least three times, via `x25519_mlkem768_sample_set_sha256`,
`_timed_material`, and the re-check at `qualified_timing.spl:486-488`.

Closing this needs one of:
1. a faster interpreted SHA-256, or
2. ~~a JIT-capable test path (today the runner forbids it at `:628-629`)~~
   — **REFUTED, see below.**

A digest-caching shortcut is **not** acceptable — it would change the pinned
receipts, which are the evidence the campaign exists to produce.

## Correction: a spec body can NEVER reach the JIT, and `:628-629` is not why

Option 2 above was wrong. Removing the forced-interpret lines would change
nothing. Two independent structural causes, both verified:

1. `src/compiler_rust/driver/src/exec_core.rs` — the doc comment on
   `run_file_jit` states *"Falls back to interpreter for code without
   `fn main()`."* A spec file is top-level `describe`/`it` with no `main`.
2. `describe`/`it`/`expect` are **Rust interpreter intrinsics**
   (`compiler/src/interpreter_call/bdd.rs`, 6 hits). Grep of
   `compiler/src/codegen/**` for each returns **0, 0, 0** — no JIT lowering
   for the BDD surface exists at all.

Paired measurement, `bin/simple run` with the engine set explicitly, identical
bodies:

| workload | interpret | jit | speedup |
|---|---|---|---|
| hot loop, with `fn main` | 63.44 s | **0.17 s** | **373x** |
| hot loop, spec form (no main) | 56.06 s | 54.12 s | **1.0x — none** |
| `sha256_text`, with `fn main` | 6.39 s | **1.60 s** | **4.0x**, digest identical |
| `sha256_text`, spec form | 6.35 s | 7.32 s | **1.0x — none** |

The 373x arm is the positive control: it proves `SIMPLE_EXECUTION_MODE=jit`
really does engage the JIT. The spec arms then prove the de-JIT is **structural
and upstream** of `:628-629`.

An opt-in `--engine=jit` flag for specs would therefore be a **false-green
generator**: a knob that appears to select an engine and measurably does
nothing, while still costing real blast radius (~15 readers of
`SIMPLE_RUNTIME_MODE` / `SIMPLE_EXECUTION_MODE`, including `font_registry.spl`,
`lsp/parser_adapter.spl`, `spec.spl:168-191`, `native_build_main.spl`).

**Leave `:628-629` alone.** Origin is `8d2a12e6270` "test: force interpreter
execution mode in test runners" (2026-07-25), whose rationale is a code comment
in the sibling hunk: a child `run <file>` must be interpreted to load the BDD
intrinsics, otherwise `simple test --mode=interpreter` can dispatch a child in
*compile* mode and yield parse errors plus zero evidence. Capability, not
builtin correctness.

### The remaining route

Measure through a `fn main` driver run under `bin/simple run`, which reaches the
JIT today and gives the real 4.0x on `sha256_text` with a byte-identical digest.
Assert on it from a spec via the sanctioned
`src/lib/nogc_sync_mut/spec/engine_probe.spl` pattern — the spec stays
interpreted and spawns a `fn main` probe under a named engine, asserting on its
verdict line. Working precedent: `test/01_unit/bugs/text_ordering_cmp_spec.spl`.
Driver scaffolding already exists under `src/app/test/x25519mlkem768_*`.

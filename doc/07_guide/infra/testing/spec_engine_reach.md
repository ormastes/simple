# Making a spec reach the engine that actually breaks

A `*_spec.spl` cannot execute under the Cranelift JIT. Any spec that pins
behaviour which differs by engine is therefore **green by construction**
against a JIT-only defect. This guide gives the mechanism for pinning a
named engine, and the two traps that make a spec look better covered than
it is.

Related: `.claude/rules/testing.md` (§ `run` and `test` are DIFFERENT
ENGINES) and
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.

## Why the demotion happens

Three layers stack. Only the third is inherent.

| # | Layer | Where |
|---|-------|-------|
| 1 | The runner pins the child's engine to `interpret` before spawning it | `src/app/test_runner_new/test_runner_single.spl:330-331`, `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:86` |
| 2 | The seed honours the pin | `src/compiler_rust/driver/src/exec_core.rs:37-38` maps `"interpret" \| "interpreter"` to `ExecutionMode::Interpret`; `:638` branches on `is_jit()` |
| 3 | A module with no `fn main` de-JITs regardless | `src/compiler_rust/driver/src/exec_core.rs:774-781` falls back to `evaluate_module` |

Layers 1 and 2 are policy and could be lifted. **Layer 3 cannot be**, and it
alone is sufficient: a spec file is top-level `describe`/`it` with no `main`,
so even `SIMPLE_EXECUTION_MODE=jit` routes it to the tree-walker.

The reason is that `describe` / `it` / `expect` are Rust **interpreter
intrinsics** with thread-local state
(`src/compiler_rust/compiler/src/interpreter_call/bdd.rs:510`, using
`BDD_INDENT` / `BDD_GROUP_STACK` / `BDD_CONTEXT_DEFS`). Grepping
`src/compiler_rust/compiler/src/codegen/**` for `"describe"`, `"it"` or
`"expect"` returns **zero hits** — there is no JIT lowering to demote *from*.
So this is not a flag to flip. The assertion has to leave the process.

## The mechanism

`src/lib/nogc_sync_mut/spec/engine_probe.spl`. The spec stays on the
interpreter and spawns a runnable probe **program** under a named engine,
then asserts on the probe's self-reported verdict line.

```simple
use std.spec.{describe, it, expect}
use std.spec.engine_probe.{engine_stdout, is_known_engine}

val _PROBE = "test/01_unit/bugs/text_ordering_jit_probe.spl"
val _PASS = "PROBE VERDICT: PASS"

describe "text ordering is correct on the JIT path (out of process)":
    it "passes the probe under the interpreter":
        expect(engine_stdout(_PROBE, "interpret")).to_contain(_PASS)

    it "passes the probe under the cranelift JIT":
        expect(engine_stdout(_PROBE, "jit")).to_contain(_PASS)
```

Chosen over the alternatives because it needs **no compiler change**, no new
directive in the spec grammar, and no per-spec opt-out plumbing — the
subprocess pattern is already established (`process_run` appears in a dozen
existing specs), so adoption cost is one import and one `describe` block.
A per-spec opt-out of the demotion would not work at all, because layer 3 is
inherent.

API (`engine_probe.spl`):

- `run_under_engine(spl_path, engine) -> (stdout, stderr, exit_code)`
- `engine_stdout(spl_path, engine) -> text` — the usual `expect` target
- `engine_verdict_passes(spl_path, engine, verdict) -> bool`
- `is_known_engine(engine) -> bool`
- `simple_binary() -> text` — resolves `SIMPLE_BINARY`, then `/proc/self/exe`,
  then `bin/simple`

## Rules for the probe program

1. **It MUST have `fn main`.** Without it, layer 3 de-JITs the probe too and
   the assertion is vacuous — you would be running the interpreter twice and
   calling it an A/B.
2. **Score the verdict LINE, not the exit code.** A codegen panic and a
   clean wrong answer both exit non-zero, and some failure shapes exit 0.
3. **Assert the interpreter column too.** Two engines agreeing is the
   evidence. One engine passing is not.
4. **Use the shape that loses static typing.** Text ordering only broke when
   codegen could not prove `TypeId::STRING` on the vreg. A literal-receiver
   probe stayed correct even pre-fix and would have been vacuous; the working
   shape passes the receiver as a function **parameter** and derives it
   (`t.substring(0, 1)`, `a.lower()`).
5. **Never spell the engine `interp`.** `SIMPLE_EXECUTION_MODE` silently
   selects the JIT on any unrecognised value, which makes an A/B look like
   agreement. `is_known_engine` rejects it up front.
6. **Observe it RED before trusting it.** See below.

## Proving the assertion is not vacuous

An assertion that has never been seen failing is not a guard. Either point
the spec at a pre-fix binary, or sabotage the codegen arm and re-run.

Worked example, `test/01_unit/bugs/text_ordering_cmp_spec.spl`, same source,
two binaries, engine named per column:

| binary | in-process examples (11) | JIT probe example |
|--------|--------------------------|-------------------|
| missing `rt_native_cmp` runtime symbol | 11/11 PASS | **FAIL** |
| complete | 11/11 PASS | PASS |

The left column is the whole problem in one row: eleven examples explicitly
written to pin text ordering were green against a binary whose JIT was
provably broken (it panicked with `missing runtime fn 'rt_native_cmp' in
lower_lt`). Only the out-of-process example moved.

## The tier-resolution trap

`use std.X` resolves to exactly one tier, and you cannot tell which by
reading the import. A WebSocket spec resolved `std.http.ws.ws_parser` to
**`nogc_async_mut` only** — sabotaging the `nogc_sync_mut` and `gc_async_mut`
copies left it green, so two of three implementations were untested behind an
import that looked tier-agnostic.

`spec` itself has this shape: **five** tiers ship a `spec/` directory —
`nogc_sync_mut`, `gc_async_mut`, `nogc_async_mut`, `gc_sync_mut`, `common`.

**Determine the tier empirically, by sabotage. Never assume.** Break the copy
you believe is being used, re-run, and confirm the spec goes red:

```
# sabotage src/lib/nogc_sync_mut/spec/engine_probe.spl, then:
bin/simple test test/01_unit/bugs/text_ordering_cmp_spec.spl   # must go RED
```

`engine_probe` was confirmed this way: sabotaging
`src/lib/nogc_sync_mut/spec/engine_probe.spl` turned 3/3 of its examples red,
so that is the file the import reaches. Then **state the tier in the spec's
docstring**, so the next reader does not have to redo it.

If a spec must cover more than one tier, it needs one example per tier with
an explicit per-tier import — a single bare `use std.X` covers exactly one.

## Checklist before claiming a spec covers a defect

- [ ] Does the defect differ by engine? If yes, an in-process `expect` cannot
      see it.
- [ ] Does the spec instantiate the type actually under test? (A 251-line,
      34-`it` WASM spec drove `WatBuilder` primitives and never constructed
      `MirToWat` at all, while its docstring claimed to validate MIR→WAT.
      Four defects survived it.)
- [ ] Which tier does each `use std.X` resolve to — verified by sabotage?
- [ ] Has each new assertion been observed RED?

## What actually runs the probes

`scripts/check/check-runnable-probes.shs`. Until 2026-08-02 the answer was
**nothing**: no hook and no workflow named a single `*_jit_probe.spl`, so the
only regression cover for the defect class specs cannot observe was asserting
nothing in practice.

The gate discovers probes by a union of two conventions under `test/` — a
basename matching `*_jit_probe.spl`, or a non-`*_spec.spl` file containing the
literal marker `PROBE VERDICT` — runs each under `interpret` **and** `jit`, and
scores the verdict LINE, never the exit code. It fails CLOSED: a missing binary,
zero probes discovered, a count below the floor, or an unrecognised engine name
is an ERROR (exit 2), never a pass. There is deliberately no opt-out file — a
suppression baseline would recreate exactly the blindness the probes exist to
close.

Wiring:

- Full run — `.github/workflows/core-mcp-dev-pipeline.yml`, which builds a
  bootstrap binary. Needs `SIMPLE_LIB=src`.
- Scorer self-test — `.github/workflows/repo-hygiene.yml`. `--self-test` drives
  25 synthetic assertions through the real scorer and enumerator, needs no
  binary, and goes red under all 14 of the branch sabotages it was checked
  against.

**Run the probes against the source root the binary will actually use.** On
2026-08-02 running them against a stale working copy reported 17 failures in
`utf8_index_space_jit_probe.spl`; every one was a fix that had already landed
upstream (`1ba2e7af34a`, `e16517c5454`, `c4a748ab774`). Against the current tree
all three probes pass on both engines. A probe failure is strong evidence, which
is exactly why the source root has to be pinned before you believe it.

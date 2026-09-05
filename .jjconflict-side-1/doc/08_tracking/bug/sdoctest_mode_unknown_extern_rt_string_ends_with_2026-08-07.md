# `bin/simple test --sdoctest <file>.md` fails on every input: `unknown extern function: rt_string_ends_with`

**Status:** Fixed (2026-08-17) — root cause confirmed and closed; the originally
reported SURFACE had already stopped reproducing for an unrelated reason, see
"Re-verification 2026-08-17" below before reading the rest of this doc.
**Found while:** implementing L1 (notebook document model + SDoctest exporter,
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` Stream L)
**Date:** 2026-08-07

## Re-verification 2026-08-17

**The reported command now PASSES, and that is NOT the fix.** On the deployed
seed, unmodified:

```
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple test --sdoctest \
    doc/06_spec/system/compiler/modules/testing/sdoctest.md
SDoctest Results: 16 total, 16 passed, 0 failed, 0 skipped, 0 errors
```

The extern gap the doc suspected was nevertheless still entirely real. It is
**lane-specific**, which is what hid it: the default engine is JIT, and the
sdoctest path stopped routing the call through the interpreter. Probing the
extern directly (`extern fn rt_string_ends_with` called by name, NOT via
`text.ends_with` — a method call can be answered by the builtin method table
without ever reaching the extern, which is why the original repro decayed):

```
SIMPLE_EXECUTION_MODE=jit          ->  ends=true  rfind=3          rc=0
SIMPLE_EXECUTION_MODE=interpreter  ->  error: semantic: unknown extern
                                       function: rt_string_ends_with   rc=1
```

Root cause, exactly as the "Suspected area" section below guessed:
`rt_string_ends_with` was registered in every codegen backend and defined in
the C runtime (`src/runtime/runtime_native.c:3670`) but had **no entry in the
seed interpreter's `EXTERN_DISPATCH` table**
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`). Identical class
to `host_wm_showcase_unknown_extern_rt_string_to_int_2026-07-28`.

`rt_string_rfind` (`src/lib/text.spl:53`, the very next line; backs
`text.last_index_of`; `runtime_native.c:3733`) had the **same** missing entry
and is fixed in the same change.

**Fix:** `rt_string_ends_with_fn` / `rt_string_rfind_fn` in
`src/compiler_rust/compiler/src/interpreter_extern/sffi_string.rs`, registered
in `interpreter_extern/mod.rs`. Byte-wise semantics mirror the C runtime
(empty needle -> subject length for `rfind`, not 0).

**Confirmed on full binaries** (coordinator, recorded as `b0a1839de71`) — all
three arms, which is what makes this a real RED->GREEN rather than a probe:

```
stale seed,  interpreter: rc=1  error: semantic: unknown extern function: rt_string_ends_with
fixed build, interpreter: rc=0  ends=true rfind=3
fixed build, jit:         rc=0  ends=true rfind=3
```

**Trap when re-running the probe: use the REPO ROOT as cwd.** From `/tmp` it
fails with `stdlib import 'std.text' resolves from the project stdlib roots
only` — a module-resolution error, on a file about text, that reads exactly
like a genuine RED. Check cwd before concluding the extern is missing again.

**Specs:** `test/01_unit/lib/text/rt_string_ends_with_extern_dispatch_spec.spl`
(calls the externs directly so it cannot go vacuous via the builtin method
table) and two Rust unit tests in `interpreter_extern/mod.rs`.

## Repro

Pre-existing and unrelated to the L1 changeset — reproduces on an untouched
in-tree doc file, no new code involved:

```bash
SIMPLE_RUST_SEED_WARNING=0 bin/simple test --sdoctest doc/06_spec/system/compiler/modules/testing/sdoctest.md
# ...
# error: semantic: unknown extern function: rt_string_ends_with
```

Also reproduces identically on a freshly generated sdoctest markdown file
produced by the new `src/app/simple_lab/export_sdoctest.spl` exporter
(`test/01_unit/app/simple_lab/export_sdoctest_spec.spl`'s
`"produces output that passes `simple test --sdoctest`"` example — left RED
per `.claude/rules/testing.md`, not weakened).

Setting `SIMPLE_LIB` explicitly does not change the outcome:

```bash
SIMPLE_LIB=$(pwd)/src SIMPLE_RUST_SEED_WARNING=0 bin/simple test --sdoctest doc/06_spec/system/compiler/modules/testing/sdoctest.md
# same error
```

Plain `bin/simple test <spec>.spl` (no `--sdoctest`) works fine on the same
binary at the same commit — the failure is specific to the `--sdoctest`
subcommand path, which self-compiles/self-executes
`src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl` (uses
`file_path.ends_with(".md")`) as part of `run_sdoctest_mode`.

**Binary tested:** `bin/simple` currently resolves to the Rust seed (`bin/simple
--version` prints the "bootstrap seed only" banner) — this is the pre-existing,
already-tracked Stage 3 self-host blocker in `.claude/rules/bootstrap.md`
("KNOWN BLOCKER (2026-08-06)"). This report only establishes that
`--sdoctest` fails on the currently-deployed seed binary; it does not
establish whether the pure-Simple self-hosted binary would reproduce the same
failure once Stage 3 is unblocked and a self-hosted binary can be deployed.

## Suspected area

`rt_string_ends_with` is a registered extern in the codegen backends
(`src/compiler_rust/compiler/src/codegen/common_backend.rs:384`,
`method_registry/builtins.rs:266`, `codegen/instr/closures_structs.rs:132,1521`,
`codegen/llvm/emitter.rs:304`), so this looks like a missing-link/missing
runtime-registration issue specific to whatever compilation path
`--sdoctest` mode uses to build/run the discovery+extractor+runner module
graph in-process, not a missing codegen rule per se.

## Impact on L1

`export_sdoctest.spl`'s output was verified structurally (contains the
expected ```` ```sdoctest ```` fence, `>>> ` prompted source, and the
captured stream output beneath the prompt — see
`test/01_unit/app/simple_lab/export_sdoctest_spec.spl`), and the notebook
document-model round trips (`.ipynb` <-> `.snb.sdn` <-> `.ipynb`) are fully
green. Only the final "run it through `simple test --sdoctest`" acceptance
step is blocked by this pre-existing, unrelated defect.

## RESOLVED 2026-08-17 — RED and GREEN both observed on full binaries

Closed end-to-end by the coordinator, same probe, three runs, rc assigned on the
line after each command:

| binary / engine | rc | output |
|---|---|---|
| stale seed (pre-fix), `interpreter` | 1 | `error: semantic: unknown extern function: rt_string_ends_with` |
| fixed build, `interpreter` | 0 | `ends=true rfind=3` |
| fixed build, `jit` | 0 | `ends=true rfind=3` |

The defect was the missing `EXTERN_DISPATCH` entry for `rt_string_ends_with` (and
`rt_string_rfind`, which backs `last_index_of`), not the reported `--sdoctest`
surface. That surface stopped reproducing only because the default engine moved
to JIT — **a decayed repro, not a fixed bug**. Pinning `SIMPLE_EXECUTION_MODE`
and comparing arms is what separated the two.

Method note for anyone re-running this: the probe must run with the repo root as
cwd. From `/tmp` it fails with "stdlib import `std.text` resolves from the
project stdlib roots only", which is a resolution error, not this defect.

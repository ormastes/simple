# `bin/simple test --sdoctest <file>.md` fails on every input: `unknown extern function: rt_string_ends_with`

**Status:** Open
**Found while:** implementing L1 (notebook document model + SDoctest exporter,
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` Stream L)
**Date:** 2026-08-07

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

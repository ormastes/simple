# Stage 2 test-runner build: `00.common/simple.sdn: project.name is missing` (2026-11-27)

**Status:** duplicate of `mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23`. A workaround is on `release/1.0.0` in `9acdac6f849` (2026-11-27 01:58, `src/lib/common/sdn/parser.spl` `parse`). The verifier run below used pinned source `06ba866385d5`, which predates it, so it still carries the miscompile. Rerun the stage-2 verification on a revision that contains `9acdac6f849`. Owner: bootstrap lane.

## Observed

The stage-2 compiler-tests verification (pinned source `06ba866385d5`, aarch64) produced neither tool:

| Task | Result | Detail |
|---|---|---|
| `compiler_cli_build` | TIMEOUT | 21603 s, artifact `producer-failed` |
| `test_runner_build` | FAIL | All 321 objects compiled and linking started; then `error: focused native-build: library-unit dyn-lib packaging failed: src/compiler/00.common/simple.sdn: project.name is missing` |

## What is known

- `src/compiler/00.common/simple.sdn` does contain `project:` / `name: simple-compiler-common`.
- On the Rust seed interpreter, `library_unit_decl_parse_v1("src/compiler/00.common", <that file>)` returns `OK name=simple-compiler-common kind=library`. So the parser source is correct for those bytes.
- The only packaging path is `library_unit_manifest_closure_v1`, which calls `library_unit_manifest_parse_v1` and then `library_unit_decl_parse_v1` (`src/compiler/80.driver/driver_build/`). Empty content would be refused earlier as `missing manifest`, so the stage-2 path received non-empty text and `root.get_path("project.name")` then `as_str()` produced `""`.

## Open questions (answered by the duplicate: a stage-2 miscompile of the inferred `trim` receiver in `parse`)

1. A native miscompile of `SdnValue.get_path` / `as_str() ?? ""` in the stage-2 compiler.
2. `load` returning different, non-empty bytes, for example a different file or a truncated read.

To tell them apart, natively build a probe that prints `content.byte_len()` and the decoded name inside `library_unit_manifest_closure_v1`'s `load`. Run it from a tracked (not gitignored) path under the checkout, with a memory cap above the ~4.5 GB per-worker estimate.

## Consequence

No qualified self-hosted `SIMPLE_BIN` or test runner exists. This blocks native qualification of the Linux orchestrator rows (`doc/03_plan/agent_tasks/simple_orchestrator_status_20261126.md`).

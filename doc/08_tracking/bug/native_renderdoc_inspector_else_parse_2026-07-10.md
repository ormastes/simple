# Native RenderDoc Inspector `Else` Parse Failure

## Resolved 2026-11-25 (release/1.0.0, worktree wt-p3-baf) — parse failure no longer reproduces

The reproduction command from this entry now passes on the tracked
`bin/simple.exe` (38,403,072 bytes) in interpreter mode:

```
SIMPLE_LIB=src bin/simple.exe test test/01_unit/app/renderdoc_replay_inspect_spec.spl --mode=interpreter
→ SPEC FILE VERDICT: outcome=OK declared>=8 executed=8 passed=8 failed=0
```

The `parse: ... Unexpected token: expected expression, found Else` failure
recorded below is gone; `src/app/test/renderdoc_replay_inspect.spl` parses and
its spec executes green. This closes the parser bug that is this entry's
subject.

Not claimed here: a live RenderDoc capture-replay run. Executing the real
RenderDoc 1.44 CLI against a canonical `.rdc` needs a RenderDoc install and a
GPU capture host, which this Windows worktree lane does not provide; that
remains app-level integration verification, not a parser defect.

## Open 2026-09-16 — needs owner triage (resolved; see banner above)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Rust-seed parser source fix and focused regression are verified; real RenderDoc
inspector execution remains pending because the application-level bootstrap
wrapper is blocked by an unrelated `rt_cli_arg_count` failure.

## Resolution status (2026-07-15)

The Rust seed parser now consumes complete inline continuation chains after
both inline-first and block-first `if` arms instead of leaving a later `Else`
token for expression parsing. One block-first regression combines inline
`elif`, `else if`, and final `else` arms so both continuation loops are covered.
The pure-Simple parser already follows the intended chain shape and required no
parallel rewrite. Focused Rust parser coverage now passes:
`cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-parser
--test control_flow` (19 tests). The full inspector source remains unexecuted;
no application-level runtime PASS is claimed.

## Reproduction

```sh
bin/simple test test/01_unit/app/renderdoc_replay_inspect_spec.spl --native
```

Observed on 2026-07-10:

```text
error: compile failed: parse: in "src/app/test/renderdoc_replay_inspect.spl": Unexpected token: expected expression, found Else
```

`bin/simple check src/app/test/renderdoc_replay_inspect.spl` passes. Three bounded native test/fix cycles removed the chained inline driver conditional and the inline struct-field status conditional, but the native parser still reports the same location-free error. `bin/simple test test/01_unit/app/renderdoc_replay_inspect_spec.spl --mode=interpreter` now confirms the same failure before execution, so it is not native code generation. Do not resume blind syntax rewrites; reduce with parser source-location diagnostics or a smaller extracted source on the next cycle.

## Impact

- `parse_renderdoc_capture_xml` and `inspect_renderdoc_capture` are implemented in pure Simple.
- The real repo RenderDoc 1.44 CLI successfully converts the canonical Vulkan `.rdc` to XML containing driver, chunks, buffers, shaders, pipelines, and dispatch actions.
- Native unit execution of the inspector remains blocked; it is not accepted as verification evidence.


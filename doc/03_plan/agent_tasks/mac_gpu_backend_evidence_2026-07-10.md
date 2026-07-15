# macOS GPU Agent Plan - 2026-07-10

## Objective

Produce deployment-grade Metal evidence and close the remaining self-hosted
GPU queue verification gap.

## Lanes

| Lane | Agent | Work | Evidence |
|---|---|---|---|
| Metal readback | Mac agent A | Run generated Metal 2D, Engine2D framebuffer, and CPU/Metal parity checks with Xcode tools. | Three dated reports; submit/readback true; zero mismatches. |
| Self-host deploy | Mac agent B | Build the pure-Simple self-hosted binary, run redeploy gate, then run queue and GPU evidence checks. | Gate log; post-swap `-c` smoke; production queue report. |
| Review | Higher-model reviewer | Check reports, platform assumptions, stale-artifact provenance, and requirement coverage. | PASS/FAIL review with exact missing evidence. |

## Status, 2026-07-11

- Metal readback lane: PASS on Darwin/arm64.
  - `check-metal-generated-2d-readback.shs`: pass, submit/readback true, zero mismatches.
  - `check-metal-engine2d-framebuffer-readback-evidence.shs`: pass, raw Metal framebuffer download proven.
  - `check-engine2d-cpu-metal-parity-evidence.shs`: pass, CPU/Metal bit-exact.
- Production queue wrapper: Metal subcheck PASS, aggregate FAIL/PARTIAL on broader non-Metal/browser gates.
  - `readback_metal_verdict=pass`
  - `metal_spark_task_status=pass`
  - `metal_normal_llm_verification_status=pass`
  - `production_gui_web_host_gpu_queue_readback_status=fail`
  - `production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met`
- Self-host deploy lane: FAIL.
  - `bin/simple` redeploy gate: `7/11 PASS (1 skipped)`.
  - `bootstrap/stage3/simple` and `bootstrap/stage3/aarch64-apple-darwin-macho/simple`: `0/11 PASS (1 skipped)` and direct execution reports `missing LC_UUID`.
  - `build/bootstrap/full/aarch64-apple-darwin/simple`: `0/11 PASS (1 skipped)` and `-c 'print(1+1)'` fails.
  - `build/bootstrap/stage3/aarch64-apple-darwin/simple`: redeploy gate timed out.
- Reviewer decision: FAIL to close TODO 119. Keep the TODO open until a fresh self-host candidate passes the redeploy gate and post-swap smoke.
- Evidence report: `doc/09_report/mac_gpu_backend_evidence_2026-07-11.md`.

## Commands

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
sh scripts/check/cert/redeploy_gate/redeploy_gate.shs build/bootstrap/full/x86_64-unknown-linux-gnu/simple
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

## Merge and Done Rules

- Merge owner: main workspace owner.
- Do not treat Linux Metal-unavailable output as Metal PASS.
- Do not accept evidence from a stale binary; record binary path and timestamp.
- Reviewer must approve before closing the TODO.
## Remaining macOS Work

- Build and install a fresh pure-Simple self-host binary containing
  `rt_host_gpu_queue_emit_payload_text` dispatch.
- Require the redeploy gate and post-swap `-c 'print(1+1)'` smoke to pass.
- Run `host_gpu_queue_roundtrip_spec.spl`; require all 16 examples to pass.
- Re-run the production queue wrapper and clear the browser first-render budget failure.
- Obtain higher-model review before closing TODO 119.

## Follow-up Evidence (2026-07-11)

- Fresh `bin/simple` bootstrap/deploy and `-c`/`run` smoke evidence passed in the bootstrap lane.
- `SIMPLE_LIB=src bin/simple test test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl --mode=interpreter --fail-fast` passed all 16 examples.
- `SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs` passed on Darwin/arm64.
  - `production_gui_web_host_gpu_queue_readback_status=pass`
  - `host_native_device_readback_status=pass`
  - `host_native_device_readback_backend=metal`
  - `browser_frame_queue_status=pass`
  - `browser_event_host_gpu_backward_completed=true`
  - `browser_first_render_under_budget=true`
- Generated evidence: `doc/09_report/production_gui_web_host_gpu_queue_readback_2026-07-11.md`.
- TODO 119 remains open until the required reviewer approval and final redeploy-gate closure decision are recorded.

## MCP Recurrence Prevention (2026-07-11)

- Root cause: `check-mcp-native-smoke.shs` forced `SIMPLE_MCP_FULL=1`, which
  bypassed the default production shell handshake implementation. The setup
  wrapper ID fix therefore had no test on the path used by default clients.
- The MCP integration spec now sends a numeric initialize ID and a string
  tools/list ID through `SIMPLE_MCP_FULL=0 bin/simple_mcp_server` and rejects a
  `null` response ID.
- The native smoke gate independently checks the same default-wrapper path
  before its full-server checks.
- Focused result: `mcp_stdio_integration_spec.spl`, 3 examples, 0 failures,
  including isolated generation from tracked `setup.shs` and nested-ID rejection.

## Final Boundary

- The fresh-cache bootstrap still failed Stage 2 and Stage 3 with the
  parameter-local LLVM defect. The Stage 4 fallback was stopped by request.
- Metal and MCP work is complete, but deployment provenance cannot be produced
  without a passing fresh candidate. TODO 119 must remain open; no stale
  `bin/simple` result may be used to satisfy the deployment criterion.

## Follow-up Evidence (2026-07-16)

- GitHub `main` was synchronized to `ca1e18c1` with the tracked-file guard
  increasing from 103052 to 103110 files.
- `bin/release/aarch64-apple-darwin/simple` is not deployable: the required
  `-c 'print(1+1)'` smoke exits zero with blank output and `check src/app/mcp`
  exits 3 without diagnostics. The canonical Mach-O symlink was restored.
- The macOS MCP gates had two host-portability defects: GNU-only `stat -c` in
  the interface-cache contract and GNU-only `date +%s%3N` timing. Both now use
  Darwin-compatible fallbacks; shell syntax, numeric millisecond output, and
  the cache-contract shell path pass locally.
- The isolated bootstrap mini-build originally failed with eight unresolved
  imports from `app.cli.bootstrap_main`. Propagating `--entry-closure` through
  `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` advances the same shard beyond those
  errors. The next `type mismatch: cannot convert dict to int` was traced to
  interpreter-native dictionaries crossing the raw-handle-only
  `rt_dict_keys` SFFI boundary. Read-only dictionary SFFI operations now accept
  both interpreter values and runtime handles; the focused Rust test passes.
- The third and final bounded mini-build cycle advanced beyond both failures
  and then stopped in phase 2 at `src/compiler/mir/mir_instructions.spl:601`:
  the bootstrap parser reports `unexpected token in class body` on the
  top-level `struct MirFunction`, followed by `expected type annotation`.
  The preserved log is `build/mini_builds/bootstrap_main_fixed.log`; no fourth
  bootstrap retry is permitted in this session.
- A focused reproduction showed that bootstrap parsing of generic `Dict`
  fields leaves the following declaration in expression mode. Moving the
  otherwise unchanged `MirModule` declaration to the end of
  `mir_instructions.spl` removes that adjacency, and the focused bootstrap
  `check` for the file now passes. This is not promoted to bootstrap evidence:
  the bounded full-build retry budget remains exhausted.
- The source-contract spec for bootstrap entry-closure propagation produced no
  output within 60 seconds under the rebuilt seed and was terminated. It is
  therefore inconclusive and is not counted as passing verification evidence.
- The tracked MCP wrapper generator previously searched only Linux release
  directories after the package candidate. It now probes arm64/x86-64 Darwin
  release and full-bootstrap artifacts as well. On this arm64 host the generated
  production wrapper selected `bin/release/aarch64-apple-darwin/simple_mcp_server`;
  initialize, tools/list, and `simple_pipe` tools/call passed with numeric and
  string request IDs preserved and `spipe: linked` returned.
- The canonical MCP native smoke still fails before its protocol phase because
  the deployed pure-Simple `bin/simple` cannot execute the interface-cache
  contract (`unknown extern function: rt_cli_arg_count`). The direct native MCP
  evidence above is valid, but the combined release gate remains failed.
- Browser hardening removed the duplicate `SimpleScriptExecutor` no-op path:
  it now delegates execution to `ScriptRunner`, drains timers/rAF, dispatches
  deterministic DOM actions, and uses the fail-closed fetch seam. The shared
  DOM dispatcher now returns registered listener actions instead of a synthetic
  `dispatch:*` placeholder. Focused source checks pass; full SSpec execution is
  withheld because the deployed pure-Simple runtime remains invalid.
- The stale Metal interpreter-self TODO was reproduced as a standalone
  struct-method call after `rt_file_exists`; the rebuilt seed returned the
  expected field value. A permanent interpreter regression was added and the
  backend comment now documents stable handle snapshots rather than a resolved
  binding workaround. The full SSpec runner remains subject to the same
  pure-Simple runtime blocker.
- Metal shutdown now transfers completion-unknown command, encoder, staged
  source, and framebuffer handles to the canonical SFFI owner. Its deferred
  reaper releases dependencies only after successful completion or registry
  release proves a terminal error; an entry with neither proof remains retained
  and blocks subsequent surface initialization. Focused source checks pass and
  the release-decision probe covers success, terminal-error, and retained-unknown
  branches. TODO 555 remains open only for current-source native failure-path
  evidence after the pure-Simple deployment gate is restored.
- A macOS-only Rust test-build defect was also fixed by applying the existing
  Linux cfg boundary to the stage-4 compiler-backfill archive test that calls
  a Linux-only helper.
- TODO 119 and TODO 531 remain open pending that next compiler fix, a fresh
  candidate, the redeploy gate, post-swap CLI/MCP evidence, and final review.
- Direct parsing of the native MCP wire stream proves five exact UTF-8
  Content-Length frames and zero stderr. The Simple validation helper still
  reports framing false after three bounded fixes (slice indexing, byte
  parsing, canonical UTF-8 encoding), so that helper/runtime disagreement is
  retained as a failed gate rather than misreported as a server defect.
- LSP native probing now requires a correlated `lsp_symbols` tools/call in
  addition to initialize and tools/list. Both installed Darwin artifacts were
  rejected because their call path still returns `Missing tool name`; the
  opt-in native wrapper exits 127 rather than caching either false green.
- The LSP JSON extractor now uses the direct-slice pattern already proven by
  the full MCP server, with focused source checking and a regression spec.
  The focused seed test runner did not complete within its single 60-second
  allowance, so only a freshly built pure-Simple native artifact may promote
  this correction to deployment evidence.
- The next cache-preserving bootstrap continuation proved the `MirModule`
  declaration-order correction in the real 421-file entry closure. It then
  exposed the same bootstrap parser state leak in two additional sources:
  `backend_types.spl` after `ClosureValue.captures: Dict<...>` and
  `type_infer_types.spl` after `Substitution.map: Dict<...>`. Both now use
  named map types at the field boundary and pass focused bootstrap checks;
  the final bounded shard cycle passed both earlier failing files before
  stopping at the third site. No fourth shard cycle was launched.
- The native-build worker selector was also Linux-only: `self_exe()` queried
  `/proc/<pid>/exe`, then silently selected stale `bin/simple` on Darwin.
  It now falls back to `ps -p <pid> -o comm=` and passes focused source
  checking. The corrected diagnostic run explicitly pinned the Rust seed and
  confirmed the worker interpreter provenance before accepting its evidence.
- The final bootstrap shard then printed line-1 `Indent`/`|` parser errors for
  otherwise clean driver sources. An exact `hir_types` -> `mir_lowering` ->
  `driver_aot_output` replay proved these were not cross-file lexer state:
  brace-bearing string literals are speculatively parsed as interpolation
  expressions, and recovered failures restored `par_had_error` but still
  emitted diagnostics under the enclosing module path. The flat bridge now
  suppresses diagnostics only for that speculative scope and restores the
  prior suppression/error state on every exit. The focused regression passes,
  and the exact replay returns 34 driver functions with no parser diagnostic.
  The unproven lexer/parser slot-identity workaround was removed. The capped
  full bootstrap shard was not rerun, so deployment and TODO 119/531/555 remain
  gated on a fresh continuation's cache-preserving build.

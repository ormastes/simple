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
  and blocks subsequent surface initialization. A registry-missing commit is
  now kept out of quarantine and the runtime owner immediately releases its
  encoder, command, and staged source; all five Engine2D dispatch paths separate
  that known-uncommitted state from committed-but-unknown completion. Focused
  source checks pass and the release-decision probe covers success,
  terminal-error, and retained-unknown branches. TODO 555 remains open only for
  current-source native failure-path evidence after the pure-Simple deployment
  gate is restored.
- Live-window click receipts now accept only completed primary-button releases;
  press events and right/middle-button releases cannot promote titlebar/body
  controls. The pure policy passes 6/6 and the gate source contract passes 7/7.
- The typed winit owner now returns the actual presentation result. The live
  host exits nonzero on initial, updated, or periodic present failure and never
  writes a positive updated event receipt before a successful present. Its
  invalid-handle guard passes 4/4.
- Chromium no longer declares a private raw present extern or clears a dirty
  tab after a failed blit; its loop returns failure. Markdown GUI returns
  nonzero and Game2D closes its native window on present failure. The shared
  caller contract passes 3/3 and all three source trees pass `check`.
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

## Detailed Continuation Lanes (2026-07-25)

Shared rules:

- Preserve unrelated working-copy changes and inspect only the assigned lane.
- Use `SIMPLE_NO_STUB_FALLBACK=1`; never deploy or certify a Rust seed.
- Run each acceptance command once, stop after three fix/verify cycles, and
  retain binary path, revision, timestamps, exit code, and report path.
- Timeout, missing artifact, stale report, CPU fallback, or unavailable host is
  not a PASS.

### Agent A: bootstrap closure and deployment

1. Start from TODO 580 and the entry-closure no-object-progress bug report.
2. Treat entry closure as resolved: the retained cycle-3 log reaches all 396
   files and `Driver start`. Do not repeat the bucket/profile cycle.
3. Resume the bounded worker at the Stage 2 owner-global repair. Require
   phase-2 completion and an artifact; declaration progress alone is not PASS.
4. Build the candidate, then run the
   canonical redeploy gate and post-swap `-c 'print(1+1)'` smoke.
5. Do not unlock GPU evidence until every deployment gate passes.

Owner-global repair detail after the 2026-07-25 three-cycle cap:

1. Owner-qualified assignments, static registration, length-encoded flattened
   binding metadata, and exact read-time refresh are complete.
2. The focused module-global suite passed 14/14.
3. The bounded Stage 2 worker produced the source-matched 20 MB bootstrap
   artifact with 679 compiled, 0 failed, and passed bootstrap sanity.
4. The first Stage 3 self-host attempt used that exact artifact for eight
   minutes at one full CPU core. It populated all 679 cache entries but timed
   out before linking, emitted no binary, and its buffered log stayed empty.
   Do not count this as a pass.
5. Resume once with
   `build/mini_cache_todo580_stage3_owner_provenance`; use a longer bounded
   deadline and require a binary plus bootstrap sanity before the canonical
   full-CLI redeploy and essential-tools smoke.
6. Keep TODO 582 separate: fresh unflattened export dictionaries still need
   owner metadata attached to the exact returned `Arc<Dict>`.

### Agent B: Linux CUDA and Vulkan evidence

1. Use only Agent A's source-matched deployed pure-Simple binary.
2. Run generated CUDA readback once; require device-origin data, exact
   pixel/checksum parity, and stable UUID identity.
3. Run generated Vulkan readback/parity once; require hardware selection,
   successful submit/readback, and exact CPU parity.
4. Record setup, transfer, and device timings separately. Classify a correct
   result below the required speedup as available-not-preferred.
5. Do not reuse the retained 2026-07-14 CUDA report as current-source evidence.

### Agent C: macOS Metal and live-window evidence

1. Run Apple Silicon first and Intel when available; Linux cannot pass this lane.
2. Re-run generated Metal 2D, framebuffer readback, CPU/Metal parity, the
   1024-pixel clip scene, and the production queue wrapper.
3. Require a real Simple Web/winit window, successful presents, keyboard and
   explicit primary-pointer interactions, and completion-only nonblank pixels.
4. Capture warm latency, max RSS, selected device identity, Xcode GPU evidence
   when required, and exact source/binary provenance.
5. Leave TODO 119 and TODO 531 open until both host rows and reviewer approval
   exist.

Merge owner: main workspace owner. Final reviewer: normal/highest-capability
model. Reject stale artifacts, CPU fallback presented as GPU evidence,
unavailable-host PASS, missing timing/RSS/device identity, or deployment
evidence not tied to the tested revision.

## 2026-07-25 handoff

Agent A's warm-cache Stage3 completed: 3 compiled, 676 cached, 0 failed in
67.1s; artifact SHA-256
`cf4834e6d8b8c5b7b148c4e86cf395f76fd5f665dd8c97bcc2f695a498056ca2`.
The canonical Stage4 remained blocked in parse and was stopped at
36,311,984 KiB RSS after 207/1,155 files. Its previously ignored
`--low-memory` flag is now propagated, but phase-2 per-file release remains
required by the existing Stage4 memory bug before Agent A retries.

TODO 582 is complete with 15/15 focused regressions. Agents B and C remain
blocked on a source-matched deployed full CLI. The macOS owner must not reuse
the Stage3 bootstrap artifact as that CLI and must keep Metal/live-window rows
open until Agent A's Stage4 and deployment gates pass.

## 2026-07-25 retention-repair review

Three read-only sidecars audited AST alias safety, source/cache correctness,
and bounded verification. The source-matched Stage3 artifact has SHA-256
`01f856054ef6f61a8dae11934d609eb4327ad586f5c7c85877d37720d567c7f1`.
The 20/40-file guards pass at 136,888 KiB, but unchanged-source native builds
still report zero cache hits. The single full Stage4 attempt reached
57,792,476 KiB RSS and about 5.0 million heap objects after 7m35s while still
parsing, then terminated without an artifact.

Agent A must implement true per-file phase-2 AST release and cache-hit
admission before another Stage4 attempt. Agents B and C remain blocked until a
deployed source-matched full CLI passes its smoke gates.

# macOS bootstrap and GPU sync evidence — 2026-07-17

Host: Apple Silicon arm64, macOS, platform triple `aarch64-apple-darwin`.

## Bootstrap

- `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift` passed.
- Stage 2 passed bootstrap compiler sanity; SHA-256: `33d74e9935b8f9afc2e8b718c4b562d953243d270b0667853f91fe71331d11ee`.
- Stage 3 passed bootstrap compiler sanity; SHA-256: `45c4d47d75b7690b8e5cc08e550f6a1ae84de1ac4d779117e797d0965a18a793`.
- Artifacts are Mach-O 64-bit arm64 executables under `build/bootstrap/stage{2,3}/aarch64-apple-darwin/simple`.
- The LLVM attempt correctly failed because the existing Rust seed was built without the LLVM feature; no Rust seed was substituted as production tooling.

## Full CLI boundary

The verified Stage 3 compiler was used for the exact Stage 4 `main.spl` entry with `--runtime-bundle core-c-bootstrap`, Cranelift, an isolated cache, and one-binary mode. The process remained CPU-active for approximately ten minutes, peaked near 7.5 GB RSS, emitted no object/cache files or diagnostics, and was stopped at the mandatory runaway ceiling. No retry was made. This leaves the provider-capsule work in TODO 535 and the Intel-host half of TODO 531 open.

A later clean Stage 3 rebuild compiled 708 units with zero failures and passed
sanity. Native module identifiers are now canonicalized independently of the
absolute workspace path (commit `70a29867`), so a hyphenated checkout no longer
produces invalid C symbols. With that compiler the focused Stage 4 path reached
provider link. The exact canonical bootstrap-mode run still emitted no output
and reached 5.8 GiB RSS after 3m42s; it was terminated on the third bounded
cycle and was not retried.

Upstream continuation then bounded physical-source closure and import
resolution. A phase-profiled exact-entry run reached native linking, exposed an
absolute-path module-identifier bug, and the corrected clean Stage 3 rebuilt
708 units with zero failures and passed sanity. Its focused Stage 4 path reached
the ordinary unresolved-provider link set. Provider-object discovery now uses
exact or underscore-delimited `runtime_<provider>` object identity for Unix,
MSVC, and MinGW shapes, avoiding suffix collisions; exact ABI scanning still
owns content validation. This is source-level progress, not a Stage 4 PASS: the
canonical wrapper still re-entered the pre-object whole-tree path and hit the
5.8 GiB bounded stop, and no later executable Stage 4 proof was recorded.

The clean Stage 3 remains a bootstrap CLI, not the deployable full CLI. Its
`compile --format=smf` path exits zero after printing `compile: <source>` but
creates no artifact, and `run src/app/cli/compile_entry.spl ...` is rejected as
an unknown command. The macOS GUI evidence owner now detects this fake success:
it requires a nontrivial SMF before launching and passes that artifact—not raw
source—to the app-bundled GUI driver.

## Metal web/GUI evidence

- Canonical surfaced browser Draw IR rendered four commands through Metal with zero skipped commands.
- Readback provenance was `device_readback`; all 76,800 pixels were nonblank.
- Artifact: `build/macos-metal-browser-backing/simple-typed-full-target.argb.json`.
- Chrome and Electron Metal backing both passed and matched each other exactly.
- The deployed July 5 full CLI remains too old for current Metal encoder externs, so the aggregate Simple/Chrome/Electron gate cannot close until a current full CLI can be deployed.

## Fresh gate refresh after parser hardening

- The Stage4 first-file `Map.keys` SIGBUS was fixed by constructing bootstrap
  frontend maps with `Map.new()`. A later generic-type closing `>` no longer
  swallows the following class dedent; the T32 mini closure and full CLI closure
  both passed the former `t32_cli/types.spl` parse failure.
- The exact full closure then exposed duplicate physical sources in phase 2.
  After 750.8 seconds only 202 of 2,095 parse entries had completed, with many
  consecutive duplicate paths, so the run was stopped under the runaway guard.
  The blocker and acceptance criteria are tracked in
  `doc/08_tracking/bug/stage4_entry_closure_duplicate_parse_2026-07-17.md`.
- Fresh Chrome and Electron captures both used ANGLE Metal on Apple M4 and
  matched bit-exactly at 320x240: 76,800 nonblank pixels and checksum
  `329775811848360` each.
- The Simple side remains fail-closed on the deployed CLI: portable Metal
  emission and framebuffer evidence stop at `rt_cli_arg_count`; current
  CPU/Metal and browser rendering stop at the missing
  `rt_metal_destroy_compute_encoder` extern.
- Building the GUI-feature host driver exposed a stale `Arc<String>` to
  `String` conversion in winit SFFI. The conversion was fixed and the documented
  GUI driver build completed in two minutes.
- The shared-MDI titlebar contract passes. The live sample emitted its full MDI
  protocol but did not leave an Aqua window. The evidence wrapper also allowed
  the launcher's AppleScript nudge to block before its own deadline; the wrapper
  now disables that redundant nudge so bounded window discovery owns the
  timeout. No live-window PASS is claimed.
- The protocol-only producer was subsequently removed as the live-gate default.
  A dedicated host now composes the same shared desktop/terminal HTML, renders
  it through `simple_web_layout_render_html_software_pixels`, and presents the
  resulting frame through winit. In the final bounded attempt the GUI seed spent
  all 45 seconds walking that dependency closure and emitted 9,977 advisory
  diagnostic lines; it exited before creating an Aqua window. The retained
  report therefore remains `window-not-found`, not a visual PASS.

## Current-source MCP/LSP evidence after `54ad67393a16`

- A preserved-cache bootstrap rebuild produced a current 24 MiB pure-Simple
  compiler with 7 compiled and 701 cached objects.
- The exact full CLI remained pre-object and was terminated at 8m24s after RSS
  reached 9.0 GiB with zero log, cache objects, or output. No repeat was made.
- That compiler built fresh current-source MCP (2.2 MiB, 53 units) and LSP MCP
  (1.1 MiB, 9 units) native artifacts directly.
- Framed initialize, tools/list, and tools/call passed for both artifacts with
  zero stderr, protocol errors, or tool errors. The LSP call returned a
  correlated id and zero `Missing tool name` occurrences.
- The canonical combined wrapper remains gated by the absent full CLI `run`
  command; direct fresh-artifact protocol evidence is retained without claiming
  the wrapper/deployment gate.

## Focused current-source Metal clip probe

- The current pure-Simple bootstrap compiler compiled the CPU/Metal parity
  harness, including a GPU-only clip scene, into a 3.5 MiB archive: 1 unit was
  compiled and 105 were reused from cache.
- Executable evidence is blocked at runtime packaging rather than Simple source
  compilation. `rust-hosted` has been removed, no installed `simple-core`
  archive exists, `core-c-bootstrap` omits the Metal host symbols, and the
  legacy Rust archive alone omits fresh C-runtime symbols.
- Three bounded link variants were attempted and then stopped at the mandatory
  iteration cap. `clip_gpu_only: MATCH` is therefore not claimed; installing a
  canonical macOS `simple-core` runtime archive is the next acceptance step.

## MCP ownership cleanup

- The obsolete `src/app/mcp/bootstrap/` prototypes were removed. Repository
  history already marks that lane superseded by `src/app/mcp/main.spl`, and its
  optimized variant could not link against current module ownership.
- `src/app/mcp/bugdb_resource.spl` is now a compatibility facade over the
  canonical `std.nogc_async_mut.mcp.bugdb_resource` implementation, eliminating
  the second mutable BugDB implementation and its stale fake-success behavior.

## Current-source host-GPU continuation

- The canonical simple-core archive builder now works with Apple `nm`, proves
  every required symbol independently, and removes per-entry `_init_all.o`
  aggregators before composition. The resulting 132 KiB archive is ABI-complete
  and no longer has duplicate `__simple_call_module_inits` owners.
- The explicit `host-gpu` lane built the current CPU/Metal parity executable
  with stub fallback disabled: 106 units compiled, zero failed, 1.4 MiB output.
- With modern one-call readback, all normal scenes are bit-exact CPU versus
  Metal. The hardened GPU-only lane retains the full mirror allocation without
  rasterizing into it and fails closed rather than returning stale pixels.
  Device readback still returns zero instead of the required 1,024 pixels, so
  `clip_gpu_only: MATCH` remains open; see
  `doc/08_tracking/bug/metal_gpu_only_native_readback_collapses_to_one_pixel_2026-07-17.md`.

## Post-rebase Simple-core and MCP closure

- The isolated lane first rebased cleanly at `c767472c`, then rebased again over
  the latest GitHub `main` at `41c736ab`; neither upstream update conflicted
  with the lane's then-current files.
- Simple-core now owns the atomic, signal/exit, sleep, asynchronous process,
  CPU-count, CLI-argument, and Unicode character-construction symbols required
  by the current MCP closure. The canonical archive-only smoke passed, exported
  every required symbol, and contained no `_init_all.o` aggregator.
- The current pure-Simple compiler built the 53-unit MCP entry with Cranelift:
  zero failed units, zero generated stubs, and a stripped 1.3 MiB artifact.
- A framed `initialize`, `notifications/initialized`, and `tools/list` exchange
  completed with exit 0, correlated responses, 1,942 output bytes, and empty
  stderr. This closes the fresh-artifact MCP runtime-owner regression without
  claiming the still-open full-CLI deployment, live-window, or GPU-only gates.

## Honest Stage3 compile continuation

- The bootstrap `compile` command now routes SMF requests through the
  pure-Simple driver, removes any stale output first, and fails closed if the
  driver creates no artifact or produces a known-stub-sized artifact (300
  bytes or less). Both `--format=smf` and `--format smf` are recognized.
- A broad self-host rebuild was rejected because it generated 157 unresolved
  stubs. A strict Rust-seed bootstrap admission was stopped after six minutes
  with no artifact, cache, or log progress. Neither artifact was accepted.
- The intended single-positional pure-Simple rebuild reached phase 2 and
  exposed the canonical labeled tuple return
  `(stdout: text, stderr: text, exit_code: i64)` as the next parser boundary.
  The bootstrap tuple parser now consumes optional `label:` prefixes while
  retaining the real element types.
- A focused current-source parser regression passes 3/3: the canonical labeled
  process result and a mixed labeled/anonymous tuple parse successfully, while
  a label with no type fails. This is stronger source behavior evidence but
  does not replace the required fresh Stage3 artifact proof.
- A post-rebase source-spec launch then found the last reserved `function`
  binding in MIR module lowering before the spec could execute. The binding is
  now `hir_fn`, consistent with bootstrap-global and per-function lowering, and
  the Stage4 source contract checks the complete three-file boundary. The
  macOS live-window source gate subsequently exits 0 through the canonical
  self-hosted launcher; repository-wide advisory warnings remain non-fatal.
- The same Stage4 contract initially exposed five semantic failures because
  literal shell `${...}` fragments were being interpreted as Simple string
  interpolation. Escaping those braces as literal text restores the intended
  script assertions; the final focused source-contract run passes 14/14.
- The three-cycle bootstrap cap is reached, so fresh Stage3, exact print-SMF,
  and live-window execution evidence remain tracked under TODO 579; no Stage4,
  Metal-native, or live-window retry was made.
- The pending live-window gate is now stronger for its next run: it requires
  Aqua focus plus delivered keyboard, pointer, and completed primary-button
  click events, and the Simple
  Web/winit host renders and records those counters instead of treating a
  static screenshot as interaction evidence.
- Press events and right/middle-button releases now fail closed instead of
  incrementing control receipts. The updated pure event policy passes 6/6 and
  the macOS gate source contract passes 7/7.
- The winit facade no longer discards `rt_winit_window_present_rgba` failure.
  Initial, event-driven, and periodic present failures stop the live host with
  a nonzero result, and updated event receipts are persisted only after a
  successful present. The wrapper guard passes 4/4; the strengthened source
  gate remains 7/7.
- The same owner result now reaches every audited hosted caller: Chromium keeps
  a tab dirty and returns false instead of accepting a failed blit, the markdown
  GUI exits nonzero, and Game2D closes its host window. Chromium, Office, and
  `src/lib` checks pass; the cross-surface contract passes 3/3.

## GPU readback runtime ownership continuation

- The GPU-only empty readback was traced to a cross-runtime managed-array
  return: Rust created the `[u32]`, while Simple-core owned length/indexing.
- Simple-core now constructs `rt_u32s_from_raw` locally from the pointer/count
  boundary. Its canonical archive is complete and exports that symbol.
- A 50 KiB strict native probe compiled with zero stubs and preserved length 3
  plus `0x00000000`, `0x7fffffff`, and `0xffffffff` bit-exactly. This proves
  the ABI repair independently of the capped full Metal scene.

## Deferred Metal submission ownership continuation

- The runtime facade now owns both deferred quarantine and immediate
  uncommitted cleanup.
- All five Engine2D submission paths distinguish a registry-missing commit
  failure from a successfully committed command whose completion is unknown.
  The first state releases encoder, command, and staged source immediately;
  only the second can transfer dependencies into quarantine.
- Focused source and ownership checks pass. TODO 555 remains open because the
  strict no-dispatch native failure probe is still blocked before entry loading
  by the capped self-hosted toolchain failure recorded in the host-toolchain bug.
- The native-lifecycle blocker no longer hides the pure state policy: a
  separate four-case interpreter unit covers retained unknown, successful
  wait, terminal registry removal, and both-proofs-present decisions without
  touching a Metal extern. It completes without a test-runner error through
  the canonical self-hosted launcher.

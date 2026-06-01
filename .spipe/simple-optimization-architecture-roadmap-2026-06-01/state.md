# Feature: simple-optimization-architecture-roadmap-2026-06-01

## Raw Request
$sp_dev sync gh often optimize simple and check with js and wasm engine optimizatikn, and gui rendering, even interpreter mode faster. first make deep detail pherallel agents plan and update progress often doc/01_research/local/simple_optimization_architecture_roadmap_2026-06-01.md

## Task Type
code-quality

## Refined Goal
Create and maintain an evidence-driven parallel-agent roadmap that coordinates Simple performance work across repository sync, JS/WASM execution, GUI rendering, and interpreter/runtime optimization without losing existing SPipe verification state.

## Acceptance Criteria
- AC-1: The roadmap file `doc/01_research/local/simple_optimization_architecture_roadmap_2026-06-01.md` contains a detailed parallel-agent plan with named lanes for sync/GitHub cadence, JS/WASM engine optimization, GUI rendering optimization, interpreter-mode speed, and cross-lane verification.
- AC-2: Each lane names concrete existing evidence sources, file/test surfaces, ownership boundaries, deliverables, metrics, and handoff gates.
- AC-3: The plan preserves existing work from related SPipe tracks instead of overwriting it, including `nodejs-js-wasm-hardening`, `simple-gui-2d-render-perf`, and `interpreter-perf-gaps`.
- AC-4: The roadmap includes a dated progress log that can be updated frequently as agents complete research, design, implementation, verification, and sync steps.
- AC-5: Sync guidance follows the repo's jj-based linear-history workflow and does not push without the required verification/approval gates.
- AC-6: Completion requires current evidence from tests, benchmarks, generated manuals, and sync state; partial planning alone is not treated as final optimization completion.

## Scope Exclusions
- This state file does not claim the full optimization roadmap has been implemented.
- This state file does not authorize unverified GitHub pushes or release actions.
- Hardware-specific GPU/WebGPU/CUDA wins require available host/device evidence or an explicit unavailable-backend record.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: code-quality).
- dev: Added the parallel-agent control plane to `doc/01_research/local/simple_optimization_architecture_roadmap_2026-06-01.md`.
- verify: PASS `sh scripts/install-spipe-dev-command.shs --check`.
- verify: PASS `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- verify: PASS `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl`.
- verify: PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (23 scenarios).
- verify: PASS `scripts/check-gtk-gui-repeat-evidence.shs`; Simple open 203 us, GTK open 68904 us, Simple frame 1 us, GTK frame 26 us, vector checksum 212444 deterministic true.
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/app/interpreter/perf_spec.spl --mode=interpreter --clean` (10 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean` (51 scenarios).
- implementation: Interpreter/runtime speed lane changed `DIAGRAM_ENABLED` loads/stores in `src/compiler_rust/runtime/src/value/diagram_sffi.rs` from `Ordering::SeqCst` to `Ordering::Relaxed`; the flag only gates recording and recorded diagram data remains protected by locks.
- verify: PASS `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`.
- verify: PASS `cargo test -p simple-runtime diagram_sffi --manifest-path src/compiler_rust/Cargo.toml` (3 tests).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/app/interpreter/perf_spec.spl --mode=interpreter --clean` (10 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean` (51 scenarios).
- implementation: GUI text-painter lane now uses pixel-width character estimates for famous-site corpus wrapping instead of treating layout width as character columns; restored the scanline y-coordinate probe required by the existing spec.
- verify: PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl`.
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild` (2 scenarios).
- docs: Regenerated `doc/06_spec/unit/browser_engine/text_painter_spec.md`; docgen completed with existing compiler warnings and reported this manual as a generated stub.
- implementation: JS/WASM lane now assimilates a fulfilled host promise whose value is another fulfilled host promise before settling the next promise, covering `Promise.resolve(navigator.gpu.requestAdapter())` inside fetched WASM instantiation callbacks.
- verification: PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_async_mut/js/engine/interpreter_async.spl`.
- verification: PASS broader JS runtime check covering `interpreter.spl`, `interpreter_async.spl`, and `interpreter_native.spl` across `nogc_sync_mut`, `gc_async_mut`, and `nogc_async_mut` affected files (7 files).
- verification: PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (106 scenarios).
- docs: Regenerated `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md`; docgen completed with existing compiler warnings and emitted a stub-style manual.
- verification: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`.
- verification: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (142 scenarios).
- implementation: Resolved the Node credential env grant path through the public `JsRuntime.grant_node_credential(...)` API instead of test-only interpreter state mutation.
- verification: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`.
- verification: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (143 scenarios).
- docs: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; docgen completed with existing compiler warnings and emitted a stub-style manual containing the explicit credential scenario.
- verification: PASS `git diff --check`.
- verification: PASS `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- sync: Non-mutating sync-safety snapshot recorded `git ls-files` count `77108`; `jj status` shows working copy `@` on top of `main` parent `test: tighten ai cli credential grant boundary` with uncommitted changes, so no fetch/rebase/push was attempted in that slice.
- sync: Current non-mutating file-count guard is `77107` after removing the local credential debug scratch file; working copy remains uncommitted, so no GitHub push was attempted.
- verify: PASS `sh scripts/install-spipe-dev-command.shs --check`.
- verify: PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl`.
- verify: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`.
- verify: PASS `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`.
- verify: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (143 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (106 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild` (2 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/app/interpreter/perf_spec.spl --mode=interpreter --clean` (10 scenarios).
- verify: PASS `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean` (51 scenarios).
- verify: PASS `cargo test -p simple-runtime diagram_sffi --manifest-path src/compiler_rust/Cargo.toml` (3 tests).
- verify: PASS `scripts/check-gtk-gui-repeat-evidence.shs`; Simple open 203 us, GTK open 68904 us, Simple frame 1 us, GTK frame 25 us, Simple text 10 us, GTK text 25 us, vector checksum 212444 deterministic true.
- verify: PASS `git diff --check`.
- verify: PASS `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- sync: PASS committed and pushed `d826cf69e0f4 perf: advance simple optimization checkpoint` to GitHub `main`; post-push fetch confirmed `main`/`main@origin` at the checkpoint, working copy clean, `git diff --check` PASS, `doc/06_spec` stray `.spl` count `0`, tracked file count `77107`.
- implementation: GUI lane added a fast vector-font unavailable fallback probe to the GTK size/speed baseline and made the repeat evidence wrapper require that fail-closed probe by default.
- verification: PASS fallback probe mode (`GTK_EVIDENCE_FALLBACK_PROBE_ONLY=1 GTK_EVIDENCE_FORCE_VECTOR_FONT_UNAVAILABLE=1`) reported `gtk_benchmark_fallback_probe_status=pass`, reason `forced-vector-font-unavailable`, zero vector-font ink pixels, deterministic true.
- verification: PASS `scripts/check-gtk-gui-repeat-evidence.shs` with fallback probe `forced-vector-font-unavailable`, Simple open 203 us, GTK open 68904 us, Simple frame 1 us, GTK frame 25 us, vector checksum 212444.
- docs: Added `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md` and updated GUI/roadmap state for AC-6 fallback evidence.
- implementation: Interpreter lane changed the shared timeout flag from `SeqCst` to `Release` stores plus `Acquire` reads in `fault_detection`, `watchdog`, and the compiler interpreter timeout test path.
- verification: PASS `cargo check -p simple-compiler -p simple-common --manifest-path src/compiler_rust/Cargo.toml`; PASS `cargo test -p simple-common timeout --manifest-path src/compiler_rust/Cargo.toml`; PASS `cargo test -p simple-compiler watchdog --manifest-path src/compiler_rust/Cargo.toml -- --test-threads=1`.
- verification: PASS interpreter perf and tiered JIT smoke specs after the timeout ordering change.
- implementation: Interpreter lane replaced formatter-based string concatenation in `src/compiler_rust/compiler/src/interpreter/expr/ops.rs` with capacity-sized `String` growth.
- verification: PASS `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`; PASS string system (33), interpreter perf (10), and tiered JIT hotspot (51) interpreter specs.
- implementation: Interpreter lane removed boxed iterator allocation from merged `CowEnv` environment scans by reusing the concrete `CowEnvIter` for `iter()`, `keys()`, and `values()`.
- verification: PASS `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`; PASS interpreter perf (10), tiered JIT hotspot (51), string system (33), Node API conformance (145), WebGPU JS/WASM Simple (106), and GTK GUI repeat evidence.
- implementation: GUI lane optimized the static-shell plan cache hot path so memory hits reuse retained decoded SWBC metadata and prepared primitive commands instead of regenerating command lists.
- verification: PASS render-cache check and HTML/CSS binary caching spec (10); PASS GTK GUI repeat evidence; PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10).
- implementation: JS/WASM hardening lane generalized native Node-compatible `child_process.spawn` process grant lookup to sanitized per-command marker keys, so non-Node commands like `git` are allowed only by explicit grant.
- verification: PASS native/runtime/spec check; PASS Node API conformance (149); PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 231 us, GTK open 71279 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444 deterministic true.
- implementation: JS/WASM optimization lane added a single-entry last-hit cache for Node-compatible `require()` lookups, bypassing the reverse cache-array scan on repeated canonical module requests while preserving alias sharing between `path` and `node:path`.
- verification: PASS JS engine check; PASS Node API conformance (150); PASS regenerated Node API manual; PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 224 us, GTK open 75025 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444 deterministic true.
- implementation: GUI/color-image lane now fails closed for bounded JPEG XL non-default structured color metadata instead of accepting it as default sRGB; the parser uses explicit available/required bit counts to avoid treating absent padded fixture bits as color metadata.
- verification: PASS image info/decode check; PASS image decode spec (75); PASS regenerated image decode manual; PASS Node API conformance (150); PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 220 us, GTK open 72130 us, Simple frame 1 us, GTK frame 28 us, vector checksum 212444 deterministic true.
- implementation: JS/WASM optimization lane routed `String.startsWith` and
  `String.endsWith` through runtime text primitives across sync, GC async, and
  no-GC async interpreter string-method families, removing duplicated
  interpreter byte loops.
- verification: PASS string-method family check; PASS Node API conformance
  (151); PASS regenerated Node API manual; PASS WebGPU JS/WASM Simple (106);
  PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open
  210 us, GTK open 77889 us, Simple frame 1 us, GTK frame 27 us, vector
  checksum 212444 deterministic true. ES5 conformance remains a pre-existing
  harness failure at 54/54 scenarios returning `nil`.
- implementation: GUI/text lane tightened the focused Google corpus Arial width
  calibration so the first `Google search` line reports width 105 against
  Chrome's 104.0625 metric, and moved the 122px first missing wrapped-line
  boundary from `site_0_google` to `site_2_facebook`.
- verification: PASS text painter check; PASS text painter spec (3); PASS
  famous-site corpus spec (37); PASS renderer smoke (9); PASS regenerated
  text-painter and famous-site manuals; PASS Node API conformance (151); PASS
  WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat
  evidence with Simple open 243 us, GTK open 77948 us, Simple frame 1 us, GTK
  frame 28 us, vector checksum 212444 deterministic true.
- implementation: Interpreter lane optimized Rust `text[index]` by preserving
  the ASCII byte-index fast path, skipping the up-front Unicode character count
  for positive in-bounds indexes, and deferring diagnostic preview allocation
  until out-of-bounds errors.
- verification: PASS string spec check; PASS string spec (47); PASS
  `cargo check -p simple-compiler`; PASS string system (33); PASS interpreter
  perf (10); PASS Node API conformance (151); PASS WebGPU JS/WASM Simple (106);
  PASS GTK GUI repeat evidence with Simple open 227 us, GTK open 69171 us,
  Simple frame 1 us, GTK frame 26 us, vector checksum 212444 deterministic true.

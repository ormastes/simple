# Simple 2D RenderDoc Backend Equivalence System Test Plan

## Test Layers

| Executable spec | Requirements | Primary evidence |
|---|---|---|
| `test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl` | REQ-001..003 | Full/minimal records, malformed classes, deterministic x10, first/all diffs |
| `test/01_unit/lib/common/renderdoc/simpleos_render_evidence_spec.spl` | REQ-016,018..021 | QEMU/board correlation and x86/AArch64/RV64 target-native SIMD receipt validation |
| `test/02_integration/rendering/backend_render_equivalence_spec.spl` | REQ-004,006 | Independent producers, completion/handles, exact oracle/pair pixels, negative controls |
| `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` | REQ-005,007,008 | Facade-only native/software Vulkan, translation labels, native-host unavailability |
| `test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl` | REQ-011 | Primitive/effect/state/resource/error/replay/100-frame matrix |
| `test/02_integration/rendering/engine2d_x86_simd_execution_spec.spl` | REQ-020,021 | Strict production facade, SSE2/AVX2 vector chunks, exact independent scalar/readback pixels |
| `test/03_system/check/renderdoc_capture_replay_inspection_spec.spl` | REQ-009 | Real replay-open; API/device/action/log/artifact; corrupt/synthetic rejection |
| `test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl` | REQ-012 | Structure-before-pixels; 50/132/43 corpus policy; tracked text divergence |
| `test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl` | REQ-013 | Profiles, rows/blockers/artifacts, elapsed/RSS, traceability |
| `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` | REQ-010,014,015 | Modern SSpec/manual/doc/sidecar/reviewer/layout contract |
| `test/03_system/os/simpleos_engine2d_guest_backend_equivalence_spec.spl` | REQ-016,018 | x86 framebuffer/VirtIO, RV64 VirtIO, ARM64 framebuffer guest-native records and exact oracle |
| `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` | REQ-017,018 | Pure-Simple QMP greeting/capabilities/screendump and serial/run/frame correlation negatives |
| `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` | REQ-018,019 | Portable descriptor and fail-closed board identity/firmware/boot/capture/transcript rows |
| `test/03_system/os/qemu/simpleos_engine2d_simd_matrix_spec.spl` | REQ-020,021 | live system-QEMU x86 SSE2/AVX2, AArch64 NEON, RV64 RVV vector chunks, instruction proof, exact scalar/QMP pixels |

## Manual-First Flow

Primary manuals expose these ordered steps: “Prepare the backend and web fixture”; “Capture independent backend render records”; “Validate provenance and frame completion”; “Compare detailed backend state”; “Compare readback against the absolute oracle”; “Report exact mismatch or host limitation”. Setup is `@inline`/`@prev`; malformed, matrix, and stress scenarios are folded; plumbing is skipped. Records/diffs use protocol capture, RDC uses artifact/log capture, aggregate uses exec capture, and screenshots are supplemental.

## Coverage and Profiles

| Profile | Corpus | Backend/device | Stress | Budget |
|---|---|---|---|---|
| focused | 6 layouts, 12 sites, 43-widget DOM | one strict Vulkan + software oracle | representative | 15m |
| intensive | all 50 layouts; all 132 reference + 24 cross-backend; 43 widget aggregate + 12 isolated | NVIDIA Vulkan, Mesa Vulkan, two translation lanes | 100 frames/case | 60m |
| QEMU | deterministic guest scene | x86_64 framebuffer/VirtIO, AArch64 framebuffer, RV64 VirtIO plus target SIMD | 10 fresh boots | bounded separate gate |
| qualification | all 132 and all 43 per backend | Linux plus native Windows/macOS | extended | scheduled |

Every REQ has at least three positive/negative or matrix assertions where meaningful. Exact pixels use zero mismatch/no tolerance. System runs use native execution; interpreter summaries are scanned for hidden failures when interpreter is used for focused syntax diagnosis.

## Gates

- Built-in matchers only; no boolean-wrapper assertions or placeholder passes.
- Generated manuals mirror all fourteen specs and report zero stubs.
- `find doc/06_spec -name '*_spec.spl' | wc -l` is zero.
- Direct env/runtime working/staged guards pass.
- Existing QEMU/GUI specs are modernized to remove inline Python, 95% comparison, auto-baseline, pass-on-init-failure, and static/pass-shaped evidence.
- Focused checks run once, then intensive once after focused is green; maximum three fix/verify cycles.

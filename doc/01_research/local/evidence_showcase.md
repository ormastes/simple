<!-- codex-research -->
# Local Research: Project Evidence Showcase

## Scope

This research maps the smallest shared path from executable SSpec evidence to a
root `EVIDENCE_SHOWCASE.md`. It covers the requested OS, server, LLM, GPU, WM,
IDE, text, still/motion, HTML, crypto/protocol, generated-manual, and
spec-to-SSpec lanes. No tests were rerun and no existing evidence was promoted
without retained provenance.

## Method and concurrent-work boundary

- Read-only sidecars inventoried SSpec/SPipe, OS/board/WM, web/database/HTML,
  and UI/IDE/media evidence. The root agent reviewed and merged their findings.
- Vendored runtime/compiler sources were excluded.
- The worktree contains many unrelated active changes. In particular,
  `src/compiler_rust/lib/std/src/tooling/migrate_spec_to_spl.spl`,
  `test/01_unit/app/tooling/spec_to_sspec_merge_spec.spl`, and its generated
  manual are active adjacent spec-to-SSpec work. This lane does not edit or
  claim them.
- No `EVIDENCE_SHOWCASE.md` currently exists in the repository.

## Existing shared infrastructure

| Concern | Existing owner | What works | Gap |
|---|---|---|---|
| SSpec assertions | `src/lib/nogc_sync_mut/spec.spl` | Direct equality, nil, contain, prefix/suffix, ordering, numeric matchers | No ordered line matcher, whitespace policy, or explicit volatile-field masks |
| Scenario evidence vocabulary | `src/lib/common/spec/scenario_evidence.spl` | Capture kinds/policy, artifact object, API/HTML/exec/binary/UI constructors | No dimensions, checksum, producer, timing, comparison, or motion fields |
| Author helpers | `src/lib/common/spec/scenario_helpers.spl` | Text/log/API/protocol/exec/binary/TUI/GUI/HTML helpers | HTML is heuristic tag stripping; capture is not automatically executed |
| Evidence integrity | `src/lib/nogc_sync_mut/spec/evidence_receipt.spl` | Presence, freshness, execution honesty, architecture, SDN serialization | Not wired to scenario artifacts or docgen |
| Doc generation | `src/app/spipe_docgen/spipe_docgen/{parser,generator}.spl` | Modern manual steps, `@capture` prose, artifact tables, TUI text and still image embedding | `@capture` is intent only; no manifest ingestion, AVIF/WebM, HTML preview, protocol-field table, or required-artifact failure |
| Still comparison | `src/os/compositor/screenshot_compare.spl` and existing QEMU/Electron capture owners | Exact/threshold/profile pixel comparison and diff image | Region/report functions are stubs; producers are fragmented |
| Structured UI evidence | `src/lib/nogc_sync_mut/ui_test/sgtti.spl`, Draw IR inspection/diff APIs | Semantic snapshots, actions/history, geometry/style evidence | Generated manuals mostly link structured JSON; interaction and visual evidence are not consistently paired |
| Artifact roots | `doc/06_spec/image/<spec-relative>/`, `build/test-artifacts/<spec-relative>/` | Documented tracked and ephemeral locations | Claimed auto-discovery is not implemented |
| Large files | `.gitattributes` | LFS for PNG/JPG/JPEG/WebP/GIF/PPM | AVIF and WebM are not covered |

The minimal owner path is therefore:

1. extend `ScenarioEvidenceArtifact` and `evidence_receipt`;
2. add shared text/HTML/protocol evidence helpers;
3. make the runner persist one fail-closed manifest;
4. make docgen consume that manifest;
5. make showcase pages link manifests and generated manuals.

Adding a separate showcase database, hashing library, capture hierarchy, or
per-feature renderers would duplicate existing owners. Shell evidence hashing
is already duplicated: at least 15 `artifact_sha256()` and 18 `sha256_file()`
implementations exist under `scripts/check`.

## Current docgen behavior and safety gaps

- Modern source form is already `use std.spec.*` with
  `describe`/`it`/`step`/`expect`. `Given_*`/`When_*`/`Then_*` is legacy.
- Supported capture kinds are `tui`, `gui`, `html`, `text`, `api`, `protocol`,
  `exec`, `binary`, `log`, and `artifact`. Motion/video is rejected metadata.
- Supported embedded image suffixes are PNG, JPG/JPEG, GIF, WebP, and SVG.
  AVIF and WebM are links only.
- `# @capture(html)` renders a label, not captured HTML.
- Metadata paths are not constrained to canonical roots. TUI embedding reads
  any existing path and places content inside a fixed Markdown fence. Broader
  embedding must first reject traversal/absolute paths and fence injection.
- HTML must not be executed inline by default. Escaped source plus structured
  DOM assertions is safe; an optional preview needs a sandbox without scripts,
  forms, navigation, or same-origin privileges.

## Evidence truth matrix

Status vocabulary for the eventual showcase should be fixed to:
`live-pass`, `historical-pass`, `contract-only`, `blocked`, `unsupported`, and
`planned`. A status without a manifest, source revision, command, artifact
checksum, and generated manual is not `live-pass`.

| Requested showcase row | Best current evidence | Honest current status | Missing proof |
|---|---|---|---|
| RISC-V Linux boot/login | `doc/09_report/rv32_media_rebuild_2026-07-25.md`; `scripts/os/check_riscv_linux_qemu.shs`; retained `build/os/rv32_soc/qemu-media-oracle.log` | `historical-pass` for RV32 | Fresh current-source receipt; RV64 login evidence |
| SimpleOS RISC-V boot and filesystem app | `test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl`; generated manual; retained `build/os/systest/riscv64.serial.log` | `historical-pass` | Retained log no longer matches current ELF; RV32 live proof |
| Linux/SimpleOS login normalization | Bespoke raw `contains`/`grep` gates and CR stripping | `contract-only` | Shared ordered-line matcher with ANSI/CR/space normalization and explicit typed masks |
| Physical ARM board | `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl`; hardening report | `blocked` | Real board identity, flash/download path, UART/SSH transcript, retained artifacts |
| Clang hello world in SimpleOS filesystem | `test/03_system/os/port/clang_static_e2e_spec.spl` and manual | `contract-only` | Live guest compile, `/hello.elf` placement, execution output and exit 42; ARM board row remains separate |
| SimpleOS web server | `scripts/qemu/qemu_rv64_http_test.shs`; July report | `historical-pass` for static `/` and `/health` | Fresh artifacts; dynamic DB-backed page and browser/DOM evidence |
| SimpleOS DB server | `scripts/qemu/check_simpleos_rv64_db_server.shs`; July report; `simple_db_service_spec.spl` | `historical-pass` for live CREATE/INSERT/SELECT, `contract-only` for broader semantics | Retained current logs and one browser-visible insert/query/update flow |
| Dynamic page open/query/insert | No integrated implementation/evidence | `planned` | Boot → page → insert → query → page reflects row; HTTP transcript, DOM assertions, still capture |
| LLM Caret TUI | `llm_caret_tui_pty_spec.spl` and generated manual | `live-pass` for offline dummy-provider TUI behavior | Does not prove local model inference |
| Simple local LLM infrastructure | `check-llm-goal-evidence.shs`; June report | Mixed: local readiness passes, strict vLLM/Torch/live dashboard rows warn/fail | Reachable local model endpoint, model identity, prompt/response receipt, Caret hello transcript |
| GPU programming | ProcessingIR specs, native backend wrappers, RenderDoc/readback reports | Mixed by backend/host | Showcase must expose emission → compile → submission → completion → device-origin readback → CPU parity as separate rungs |
| SimpleOS QEMU WM | July 19 WM fullscreen report and QMP/PPM flow | `historical-pass`; newest July 28/29 reports fail | Fresh current-source artifact bundle; event receipts paired with frames |
| IDE | Office/IDE system manuals and TUI evidence | `live-pass` for contract/TUI suite; GUI proof absent | Production IDE launch, edit/action/diagnostic/run receipt, still and short motion artifact |
| Crypto/protocol bitfields | `scenario_binary_detailed_evidence`; one bespoke NVMe bit table | `contract-only` | Typed field rows with offsets, widths, masks, endianness, expected/actual, importance, raw-byte linkage |
| Motion/event evidence | None | `planned` | Event transcript + keyframe hashes + WebP/WebM presentation; no byte-exact video oracle |

## Representative exact paths

### OS and WM

- `test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl`
- `test/03_system/os/port/clang_static_e2e_spec.spl`
- `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`
- `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl`
- `test/03_system/gui/arm64_wm_ramfb_screendump_spec.spl`
- `scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`
- `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-19.md`
- `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-28.md`

### Web and database

- `src/os/kernel/boot/http_baremetal.spl`
- `src/os/services/database/simple_db_service.spl`
- `scripts/qemu/qemu_rv64_http_test.shs`
- `scripts/qemu/check_simpleos_rv64_db_server.shs`
- `test/03_system/os/simpleos_riscv_network_gate_spec.spl`
- `doc/09_report/verify_simpleos_filesystem_toolchain_servers.md`

The current root page is static. There is no existing DB-backed dynamic page
or browser-open/query/insert system evidence. The smallest exemplar should
reuse the existing boot HTTP service and `SimpleDbService`, not add another
server.

### LLM, GPU, IDE

- `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl`
- `scripts/check/check-llm-goal-evidence.shs`
- `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`
- `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl`
- `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
- `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl`

## Text verification design constraints

One common helper should:

1. strip ANSI and normalize CRLF;
2. split into lines and retain line boundaries;
3. optionally trim ends or collapse nonempty horizontal whitespace;
4. apply named masks only to declared fields such as `date`, `version`,
   `address`, `duration`, and `build_id`;
5. require selected lines in order, with optional bounded gaps;
6. report the first missing/out-of-order line and retain raw plus normalized
   transcripts.

It must not delete all whitespace, ignore all matching lines, reorder content,
or silently mask an undeclared pattern. Linux boot/login and SimpleOS boot/login
should share the helper and differ only in their declarative line expectations.

## Still and motion verification constraints

- Semantic/structured assertions come first: SGTTI, Draw IR, DOM, protocol,
  serial, or event receipts.
- Still evidence proves appearance/layout. Use lossless PNG/WebP for pixel
  baselines; SVG only for native vector/diagram producers; AVIF is presentation
  compression, not the canonical pixel oracle.
- Motion evidence proves temporal/event behavior. Verify event order, target,
  timestamps/durations within tolerance, and selected keyframe hashes/pixels.
  WebM or animated WebP is a review artifact, not a byte-exact oracle.
- Git LFS should be threshold/policy driven and cover selected binary formats;
  do not migrate all historical artifacts merely because a new suffix is added.

## HTML and protocol presentation constraints

- HTML evidence should retain sanitized/escaped source, visible text, selector
  and attribute assertions, response headers/status, and an optional still.
- Generated Markdown should not execute captured scripts. A richer local doc
  viewer may use a sandboxed iframe, but GitHub-facing output needs a safe
  fallback link/source/still.
- Protocol evidence should retain raw bytes and machine assertions while
  rendering a human table:
  `offset | bits | mask | field | endian | actual | expected | status | note`.
- Highlighting is derived from typed `important`/`severity` metadata, not raw
  HTML supplied by a test.

## Spec-to-SSpec status

Contrary to older plans, an active adjacent implementation now exists in
`src/compiler_rust/lib/std/src/tooling/migrate_spec_to_spl.spl`. It extracts
Markdown examples, emits a generated region, preserves manual content through
`merge_generated_spec`, and uses `pending(...)` where no oracle exists.

This remains a separate lane because:

- the source file and its new test/manual are concurrently dirty;
- unsupported examples still require domain-specific oracles;
- the generated test currently includes a boolean-wrapper assertion that does
  not meet this lane's modern-SSpec requirement;
- evidence schema and capture execution need to stabilize before the generator
  can emit correct evidence scenarios.

The evidence plan should integrate with that generator later through a versioned
manifest/schema, not duplicate it or block the showcase MVP on broad migration.

## Minimal recommended delivery sequence

1. Truthful root/subproject showcase convention consuming existing manuals and
   receipts.
2. One versioned `ScenarioEvidenceArtifact`/receipt manifest, canonical paths,
   path/content safety, and fail-closed required evidence.
3. Shared normalized ordered-text matcher; migrate one Linux and one SimpleOS
   boot/login exemplar.
4. Safe docgen rendering for still, motion link/player fallback, HTML source +
   structured checks, and protocol field tables.
5. One end-to-end exemplar each for QEMU WM/IDE interaction and SimpleOS
   dynamic page + DB insert/query.
6. Local-model Caret hello and strict GPU rows only where the required host
   produces live receipts.
7. Spec-to-SSpec evidence generation after the schema is stable.

This sequence reuses existing owners, fixes false-green evidence before adding
presentation, and avoids a new framework beside the unfinished capture plan.

<!-- codex-design -->
# System Test Plan: Evidence Showcase

## Status

Design complete; executable scenarios are created during implementation after
their production APIs exist. This plan forbids placeholder/silent-green specs.

## Scope

Verify:

- manifest schema, receipt adaptation, status derivation, artifact integrity,
  and path safety;
- normalized ordered boot/login text;
- still and motion evidence;
- inert HTML and dynamic DB page evidence;
- typed protocol/crypto evidence;
- root/subproject showcase generation and discoverability;
- QEMU WM, IDE, local LLM, GPU-rung, and physical ARM truth boundaries; and
- workflow/manual/modern-SSpec consistency.

## Frozen authoring vocabulary

Every new/updated spec uses:

```simple
use std.spec.*
```

Primary manual flow:

```simple
step("Capture the feature evidence")
step("Verify the structured evidence")
step("Render the evidence for review")
step("Publish the showcase link")
```

Shared setup/checker names:

- `prepare_evidence_workspace`
- `check_text_evidence`
- `check_visual_evidence`
- `check_html_evidence`
- `check_protocol_evidence`

Temporary helpers must call `fail(...)` or `assert(false)` until implemented.
No Given/When/Then helpers, boolean-wrapper assertions, custom matchers,
`pass_todo`, empty helper bodies, missing-artifact success, or executable specs
under `doc/06_spec`.

## Planned executable and manual paths

| Lane | Executable SSpec | Generated manual |
|---|---|---|
| Core/showcase/docgen | `test/03_system/app/testing/feature/evidence_showcase_spec.spl` | `doc/06_spec/03_system/app/testing/feature/evidence_showcase_spec.md` |
| Linux RISC-V text | `test/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.spl` | `doc/06_spec/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.md` |
| SimpleOS text | `test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl` | `doc/06_spec/03_system/os/evidence/simpleos_rv64_login_evidence_spec.md` |
| Dynamic DB HTML | `test/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.spl` | `doc/06_spec/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.md` |
| QEMU WM | update `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` | `doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md` |
| IDE | `test/03_system/app/ide/feature/ide_interaction_evidence_spec.spl` | `doc/06_spec/03_system/app/ide/feature/ide_interaction_evidence_spec.md` |
| Local Caret | `test/03_system/app/llm_caret/feature/llm_caret_local_model_hello_evidence_spec.spl` | `doc/06_spec/03_system/app/llm_caret/feature/llm_caret_local_model_hello_evidence_spec.md` |
| GPU rungs | `test/03_system/app/simple_2d/gpu_evidence_rung_matrix_spec.spl` | `doc/06_spec/03_system/app/simple_2d/gpu_evidence_rung_matrix_spec.md` |
| Protocol/crypto | `test/03_system/app/testing/feature/protocol_evidence_table_spec.spl` | `doc/06_spec/03_system/app/testing/feature/protocol_evidence_table_spec.md` |
| Physical ARM | update `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` | `doc/06_spec/03_system/os/simpleos_physical_board_render_evidence_spec.md` |
| UI evidence audit | update `test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` | existing mirrored manual |

## Scenario design

Every mapped behavior has at least a happy/accepted case, an edge/blocker case,
and an invalid/fail-closed case.

### A. Core manifest, showcase, and docgen

Primary spec: `evidence_showcase_spec.spl`.

1. Happy: valid v1 manifests generate unique critical rows with requirements,
   modern SSpec, manuals, receipts, artifacts, statuses, and root/subproject
   links.
2. Edge: unknown minor fields are tolerated; unavailable hardware publishes a
   blocker with prerequisite, resume command, owner, and reviewer.
3. Error: reject unsupported major, duplicate row/manifest ID, missing required
   field/artifact, stale current claim, absolute/traversal/symlink escape,
   MIME/suffix mismatch, unsafe Markdown/HTML, and hand-authored `live-pass`.

Also verify:

- `FILE.md` declares `EVIDENCE_SHOWCASE.md`;
- `config/FILE.md` declares `config/evidence_showcase.sdn`;
- `README.md` links the root showcase;
- generated-region merge preserves human prose;
- every critical row has complete traceability; and
- no executable `.spl` exists under `doc/06_spec`.

### B. Linux and SimpleOS text

Each text spec has:

1. Happy: real current runner transcript passes ordered login/shell actions
   after ANSI/CRLF normalization and declared date/version masks.
2. Edge: bounded gaps and collapsed horizontal whitespace pass without losing
   line order/boundaries.
3. Error: missing/out-of-order line or invalid mask shape fails with expected
   index, actual line, nearby lines, and raw/normalized artifact paths.

Linux-specific:

- reuse `scripts/os/check_riscv_linux_qemu.shs`;
- RV32 and RV64 remain separate evidence;
- media/source hashes and current revision must match.

SimpleOS-specific:

- harden the serial-shell producer;
- require actual password acceptance, prompt, `ls` result, and launched
  command/tool result;
- echoed input or QEMU `|| true` cannot satisfy the gate.

### C. Still and motion: WM and IDE

Each UI spec has:

1. Happy: semantic UI-access/SGTTI/Draw IR assertions precede baseline/action/
   post keyframes and ordered event receipt.
2. Edge: lossless still plus valid bounded WebP/WebM review media remains
   presentation-only and includes accessible transcript/summary.
3. Error: missing event/keyframe, wrong hash/dimensions/baseline, nonmonotonic
   events, duration/size limit breach, or production SGTTI import fails.

WM uses the existing current-source fullscreen producer. Latest failures
override historical PASS.

IDE must execute the actual production IDE/editor route. Office suite or
feature-check TUI evidence cannot substitute.

### D. Dynamic SimpleOS page and DB

1. Happy: QEMU boot/readiness → initial dynamic GET → insert → select → refreshed
   GET observes row, with correlated serial/API/HTML/DB/still artifacts.
2. Edge: escaped row content, selector/attribute/visible-text checks, and
   harmless unknown response header remain valid.
3. Error: missing readiness/status/row/still, query mismatch, uncorrelated run
   IDs, unsafe executable HTML preview, or artifact path escape fails.

### E. Protocol/crypto field table

1. Happy: known raw bytes produce typed field rows and deterministic links from
   table fields to numbered raw bytes.
2. Edge: unaligned/multibit fields and an unknown noncritical field remain
   explicit and accessible.
3. Error: overlap, out-of-range bit/byte width, mask/value mismatch, invalid
   endianness, or highlight without typed status/importance fails.

### F. Local LLM Caret

1. Happy: loopback Simple-compatible endpoint lists a concrete model; Caret
   sends `hello`, receives nonempty local model output, and retains
   endpoint/model/request/response/PTY provenance.
2. Edge: streamed chunks assemble deterministically and retain order.
3. Error: dummy/mock provider, nonloopback endpoint, unreachable server, wrong
   model identity, fixture marker, or missing transcript cannot claim local
   inference; an honest blocker row is allowed.

### G. GPU rung matrix

1. Happy: each available backend separately proves emission, compile/validate,
   submit, completion/fence, device-origin readback, and exact CPU parity.
2. Edge: first unavailable rung stops promotion and records target-specific
   blocker/resume information.
3. Error: source scan as compile, CPU fallback, handle zero, synthetic
   completion, non-device readback, or missing parity cannot promote a later
   rung.

The matrix aggregates existing backend receipts; it does not add or execute a
new backend.

### H. Physical ARM

1. Happy (only on selected/prepared hardware): board ID + flash/boot + in-guest
   Clang compile/link + filesystem placement + execution output/exit/UART.
2. Edge: unavailable board publishes a valid blocker with exact profile,
   prerequisites, artifacts, owner/reviewer, and resume command.
3. Error: QEMU, host compile, MCU catalog/source presence, or programming-only
   log cannot claim physical Linux-class ARM execution.

## Requirement traceability

| Requirement | Specs | Cases | Coverage |
|---|---|---:|---|
| REQ-EVS-001, REQ-EVS-002, REQ-EVS-003, REQ-EVS-004, REQ-EVS-005 | Core/showcase | 3+ each | Full |
| REQ-EVS-006, REQ-EVS-007 | Linux + SimpleOS text | 3 each/spec | Full |
| REQ-EVS-008, REQ-EVS-009 | WM + IDE | 3 each/spec | Full |
| REQ-EVS-010, REQ-EVS-012 | Dynamic DB HTML | 3 each | Full |
| REQ-EVS-011 | Protocol/crypto | 3 | Full |
| REQ-EVS-013 | WM | 3 | Full |
| REQ-EVS-014 | IDE | 3 | Full |
| REQ-EVS-015 | Caret | 3 | Full |
| REQ-EVS-016 | GPU matrix | 3 | Full |
| REQ-EVS-017 | Physical ARM | 3 | Full |
| REQ-EVS-018, REQ-EVS-020, REQ-EVS-021 | Core/showcase | 3+ each | Full |
| REQ-EVS-019 | Core + all changed specs + UI audit | 3+ | Full |

## NFR traceability

| NFR | Verification |
|---|---|
| NFR-EVS-001 | Receipt freshness/status happy/blocker/stale cases |
| NFR-EVS-002 | Major reject, minor tolerate, missing-field reject |
| NFR-EVS-003 | Path/root/symlink/MIME/Markdown/HTML security cases |
| NFR-EVS-004 | Canonical tracked/ephemeral path and LFS policy audit |
| NFR-EVS-005 | Still/motion size, duration, transcript, keyframe cases |
| NFR-EVS-006 | Focused median ≤1s; one inventory pass/full ≤10s; hot-path source audit |
| NFR-EVS-007 | First mismatch + bounded raw/normalized artifacts + 4 MiB stream cap |
| NFR-EVS-008 | Cross-host blocker record completeness |
| NFR-EVS-009 | Alt/summary/transcript/non-color status and manual review |
| NFR-EVS-010 | 100% critical row traceability aggregate |

No requirement has zero planned cases.

## Capture and manual policy

| Lane | Capture kinds | Visible manual evidence |
|---|---|---|
| Boot/login | `text`, `log`, `exec` | compact normalized excerpt; raw/normalized links |
| Dynamic page/DB | `api`, `html`, `gui`, `log` | response/DOM table, inert source, still |
| WM/IDE | `protocol`, `gui`, `motion`, `artifact` | event table, keyframes, transcript/media links |
| Caret | `api`, `text`, `exec` | endpoint/model and conversation transcript |
| GPU | `protocol`, `binary`, `log`, `artifact` | rung table and retained readback links |
| Crypto/protocol | `binary`, `protocol`, `text` | field table and raw byte anchors |

Primary scenarios are visible. Reusable setup is `@inline`; visible flows
include it with `@include`/`@prev`. Edge/error/matrix details are folded.
Executable SSpec is folded last. Default display remains `embed_tui`; explicit
`embed_all` is used only when the manual benefits.

## Environment and dependency order

1. Pure manifest/text/protocol/motion unit fixtures.
2. Runner persistence and docgen fixture tests.
3. Linux/SimpleOS text vertical slices.
4. Dynamic DB HTML.
5. WM and IDE.
6. Caret on prepared local-model host.
7. GPU matrix on each prepared native host.
8. Physical ARM only after profile/hardware selection.
9. Aggregate showcase, workflow, and UI evidence audits.

Unavailable native hosts produce explicit blocker evidence; they are not
skipped, excluded, or counted as feature PASS.

## Pass/fail criteria

PASS requires:

- all applicable focused specs execute with direct assertions;
- every generated manual reports zero stubs and reads as an operator manual;
- required evidence cannot disappear silently;
- root/subproject status derives from validated manifests;
- all security/path/media negative fixtures fail closed;
- NFR measurements meet targets;
- traceability is 100%; and
- an independent highest-capability reviewer accepts manual quality and claim
  boundaries.

## Smallest one-pass verification set

During implementation:

1. Run each changed focused spec once in self-hosted native mode with stub
   fallback disabled.
2. Generate each changed manual once with `spipe-docgen --no-index`; require
   complete/zero stubs and inspect it once.
3. Run the existing UI evidence audit once after all UI paths settle.
4. Run the generated-spec layout guard once; require zero executable specs in
   `doc/06_spec`.
5. Run the central evidence-showcase aggregate once.
6. Run working/staged direct-env-runtime guards once at final verification.

Do not rerun unchanged green commands. Stop after three fix/verify cycles and
report remaining failures.

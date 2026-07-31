<!-- codex-design -->
# Detail Design: Evidence Showcase and Reviewable SSpec Evidence

## Status

Implemented design for selected requirements `REQ-EVS-001..021` and
`NFR-EVS-001..010`.

## Design principles

1. Existing semantic/runtime owners prove behavior.
2. One manifest joins receipts, artifacts, manuals, and showcase rows.
3. Structured assertions decide PASS; media explains the result.
4. Missing or stale required evidence fails closed.
5. Production entrypoints do not import or execute evidence machinery.
6. Modern SSpec is the only new/updated authoring style.

## Existing components retained

| Component | Retained responsibility |
|---|---|
| `ScenarioEvidenceArtifact` | Scenario/step evidence identity and payload |
| `scenario_helpers.spl` | Producer-facing capture/check constructors |
| `EvidenceReceipt` | Pure execution honesty, artifact presence/freshness, target checks |
| QEMU/Electron/compositor owners | Capture and pixel comparison |
| SGTTI/UI access/Draw IR/CDP | Structured UI/DOM interaction assertions |
| SSpec runner | Scenario execution and final result |
| SPipe docgen | Manual generation and evidence presentation |

The proposed generic `Capture` trait/registry from
`doc/05_design/sspec_capture_extension.md` is not implemented in this lane.
Its useful typed compare-policy ideas are retained, but a registry and
user-defined rendering plugins are unnecessary for the selected exemplars.

## Data structures

### Artifact integrity

Keep `ScenarioEvidenceArtifact` stable and join persisted-file integrity by
path:

```simple
pub struct ScenarioArtifactIntegrity:
    path: text
    format: text
    mime: text
    width: i64
    height: i64
    required: bool
    capture_ready: bool
    byte_size: i64
    checksum: text
    producer: text
    producer_version: text
    source_revision: text
    host: text
    target: text
    baseline_identity: text
    comparison_result: text
```

Every persisted artifact must have a matching integrity row before docgen or
showcase publication. This avoids widening all existing artifact constructors.

Add `motion` to `ScenarioCaptureKind`. `gui` remains a still image; motion is
not overloaded onto GUI capture.

### Text evidence

`src/lib/common/spec/scenario_text_evidence.spl`:

```simple
pub enum ScenarioTextMask:
    date
    version
    address
    duration
    build_id

pub struct ScenarioTextEvidencePolicy:
    trim_lines: bool
    collapse_horizontal_whitespace: bool
    masks: [ScenarioTextMask]
    max_gap: i64

pub struct ScenarioTextMatchResult:
    passed: bool
    first_expected_index: i64
    first_actual_index: i64
    diagnostic: text
    raw_transcript: text
    normalized_transcript: text
```

Public helper:

```simple
pub fn check_text_evidence(
    actual: text,
    expected_lines: [text],
    policy: ScenarioTextEvidencePolicy
) -> ScenarioTextMatchResult
```

ANSI and CRLF normalization and ordered matching are always enabled. Date,
version, address, duration, and build-id masks validate source shape before
replacement. A failed mask shape is a mismatch.

### Motion evidence

`src/lib/common/spec/scenario_motion_evidence.spl`:

```simple
pub struct ScenarioMotionEvent:
    sequence: i64
    time_ms: i64
    kind: text
    target: text
    value: text
    status: text

pub struct ScenarioMotionKeyframe:
    time_ms: i64
    artifact_path: text
    oracle: text
    status: text

pub struct ScenarioMotionEvidence:
    duration_ms: i64
    events: [ScenarioMotionEvent]
    keyframes: [ScenarioMotionKeyframe]
    transcript_path: text
    review_media_path: text
```

Validation requires:

- duration `0..10000` ms;
- monotonic event sequence and timestamps;
- keyframes within duration;
- at least two keyframes;
- transcript present;
- review media at most 8 MiB when retained; and
- every keyframe refers to a validated still artifact.

Review media never contributes to the truth value.

### Protocol fields

`src/lib/common/spec/scenario_protocol_evidence.spl`:

```simple
pub struct ScenarioProtocolFieldEvidence:
    byte_offset: i64
    byte_length: i64
    bit_offset: i64
    bit_width: i64
    mask: text
    endianness: text
    name: text
    actual: text
    expected: text
    status: text
    importance: text
    note: text
```

Rows are sorted by byte/bit offset. Validation rejects negative/out-of-range
locations, overlapping declared fields unless explicitly allowed by the decoder,
invalid widths/masks/endianness, and actual/expected mismatch with `pass`.

### Manifest

`src/lib/nogc_sync_mut/spec/scenario_evidence_manifest.spl`:

```simple
pub struct ScenarioEvidenceManifest:
    schema_major: i64
    schema_minor: i64
    feature_id: text
    requirement_ids: [text]
    spec_path: text
    generated_manual_path: text
    scenario_id: text
    step_id: text
    required: bool
    result: text
    showcase_status: text
    reason: text
    source_revision: text
    source_digest: text
    command: text
    producer: text
    producer_version: text
    host: text
    target: text
    backend: text
    start_time: i64
    duration_ms: i64
    artifacts: [ScenarioEvidenceArtifact]
    artifact_integrity: [ScenarioArtifactIntegrity]
    text_results: [ScenarioTextMatchResult]
    motion_evidence: [ScenarioMotionEvidence]
    protocol_fields: [ScenarioProtocolFieldEvidence]
    html_checks: [ScenarioHtmlCheckResult]
    blocker_prerequisite: text
    resume_command: text
    owner: text
    final_reviewer: text
```

Typed detail arrays are validated when their artifact kinds are declared.

Public surface:

```simple
pub fn scenario_evidence_manifest_to_sdn(
    manifest: ScenarioEvidenceManifest
) -> text

pub fn scenario_evidence_manifest_from_sdn(
    source: text
) -> Result<ScenarioEvidenceManifest, text>

pub fn validate_scenario_evidence_manifest(
    manifest: ScenarioEvidenceManifest
) -> Result<ScenarioEvidenceManifest, text>

pub fn manifest_from_evidence_receipt(...) -> ScenarioEvidenceManifest
```

## Manifest status algorithm

Status is computed after receipt and artifact validation:

1. unsupported target → `unsupported`;
2. explicit unavailable prerequisite or latest required execution failure →
   `blocked`;
3. no executable scenario → `planned`;
4. executable scenario but no qualifying live receipt → `contract-only`;
5. verified PASS whose source/producer/target freshness no longer matches →
   `historical-pass`;
6. current verified PASS and all required artifacts/checks valid →
   `live-pass`.

An input `showcase_status` is accepted only as the output of this algorithm.
Docgen recalculates and rejects disagreement.

## Artifact path validation

Accepted paths are repository-relative and beneath exactly:

- `build/test-artifacts/`
- `doc/06_spec/image/`

Validation:

1. reject empty, absolute, drive/UNC, scheme, query/fragment, control/NUL, `.`,
   or `..` components;
2. resolve repository root, allowed root, and candidate through the existing
   canonical path owner;
3. require candidate identity below `canonical_root + "/"`;
4. require a regular non-symlink-followed file;
5. compare size and SHA-256 to the manifest;
6. read only within a bounded limit; and
7. recheck identity/size after reading.

Links are computed relative to the generated manual directory and URL-encoded;
manifest path text is never inserted directly into Markdown.

## MIME, suffix, and evidence roles

| Role | Accepted format | Oracle rule |
|---|---|---|
| Pixel still | `.png`, lossless `.webp` | Existing pixel comparison receipt |
| Vector-native still | `.svg` | Producer must declare vector-native |
| Presentation still | `.avif`, legacy JPEG/GIF | Requires canonical still fallback |
| Presentation motion | animated `.webp`, `.webm` | Requires event receipt + keyframes |
| Text/TUI/log | declared plain/ANSI/log suffix and MIME | Text matcher/check result |
| HTML | `.html` artifact | DOM/source checks; never executed by Markdown |
| Protocol raw | `.bin` plus `.hex.txt` view | Exact bytes + typed field checks |

`.gitattributes` gains `*.webm` only when the first retained WebM is committed.
AVIF LFS tracking is deferred until an AVIF artifact is selected. This avoids
speculative repository policy.

## Markdown rendering safety

- Tables escape backslash before pipe and flatten CR/LF.
- Alt text escapes brackets/backslashes and includes a textual claim summary.
- Links use encoded, validated relative destinations.
- Fenced evidence uses one more backtick than the longest run in the content.
- Redaction runs before Markdown escaping.
- Embedded text is length-bounded and links to the full artifact when truncated.
- Captured HTML is always inert fenced `html` text.
- Protocol importance/status renders as text such as `CRITICAL` and `FAIL`;
  color is supplemental only.

## Runner integration

The pure-Simple runner:

1. derives `build/test-artifacts/<spec-relative>/evidence.sdn`;
2. passes that path through the existing test context, not
   `SIMPLE_TEST_RESULT_FILE`;
3. executes the scenario/producer;
4. collects existing artifacts/check results;
5. composes or adapts the receipt;
6. validates the manifest;
7. writes atomically; and
8. fails the scenario when required evidence is absent or invalid.

The Rust seed is not extended. Production application entrypoints never see the
manifest path.

## Docgen integration

Add one focused module:

`src/app/spipe_docgen/spipe_docgen/evidence_manifest.spl`

It parses/validates the manifest into render fragments. This avoids enlarging
the already large parser/generator files.

Focused generation derives one manifest path from the source spec. No scan or
cache is needed in v1.

Generated manual order:

1. evidence-at-a-glance summary;
2. primary operator steps with step-local evidence;
3. edge/error/matrix details folded;
4. reproduction/diagnostics folded; and
5. executable SSpec folded last.

## Showcase generation

`config/evidence_showcase.sdn` is the curated row inventory:

```sdn
evidence_showcase:
  row:
    id: simpleos.web_db.dynamic_page
    category: web_database
    title: SimpleOS dynamic page and database
    requirement: REQ-EVS-012
    spec: test/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.spl
    manual: doc/06_spec/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.md
    owner: simpleos
```

`status`, `freshness`, and artifact links are forbidden in this config.

`spipe-docgen --showcase`:

1. parses the inventory;
2. rejects duplicate row IDs or missing traceability;
3. derives each manifest path;
4. validates each row once;
5. sorts by configured category/order;
6. renders summary counts and critical tables; and
7. replaces only the delimited generated region.

Root `EVIDENCE_SHOWCASE.md` and selected subproject showcases use the same
contract. The root page links subprojects; it does not duplicate artifacts.

## Root showcase layout

```text
# Simple Evidence Showcase

Truth notice and generated revision

## Review in 30 seconds
1. Choose a capability.
2. Read the status and exact claim boundary.
3. Open proof links or the blocker resume command.

## Status summary
status | count | meaning

## Critical capabilities
capability | status | proved claim/boundary | target/freshness | proof | resume

## Recent evidence
## Subproject evidence
## Status meanings and freshness policy
```

No remote status badges are used. Status is always literal text.

Initial subproject hubs:

- `src/os/EVIDENCE_SHOWCASE.md`
- `src/app/ide/EVIDENCE_SHOWCASE.md`
- `src/app/llm_caret/EVIDENCE_SHOWCASE.md`
- `src/lib/gc_async_mut/gpu/EVIDENCE_SHOWCASE.md`

Do not create one showcase per individual RISC-V or backend lane.

## Exemplar integration

### Linux RISC-V login

Reuse `scripts/os/check_riscv_linux_qemu.shs` and its terminal probe. Move the
ordered transcript oracle to `check_text_evidence`. RV32 and RV64 remain
separate rows; historical RV32 evidence cannot imply RV64.

### SimpleOS login

Harden `scripts/qemu/check_simpleos_rv64_serial_shell.shs`: remove
success-through-`|| true`, require bounded process completion, ordered
login/password/prompt/`ls`/known-result/tool-output evidence, and reject echoed
input as execution proof.

### Dynamic DB page

Add one dynamic GET route to the existing `http_baremetal.spl` owner that
renders rows from `SimpleDbService`. Reuse the current HTTP/DB server and QEMU
producer. Do not add another web or DB server.

### QEMU WM

Update the existing fullscreen spec/wrapper. The latest current receipt wins
over historical reports. Event sequence and changed/restored keyframes decide
PASS; WebM/WebP is presentation only.

### IDE

The current IDE entrypoint only prints startup readiness. First connect the
canonical IDE command to the existing production editor launch route, then
prove edit/action/diagnostic/run interaction. Office plugin evidence cannot
substitute for IDE UI execution.

### Local LLM

Use the existing OpenAI-compatible Caret client and local runtime readiness
probe. Require loopback endpoint, model listing/identity, `hello`, nonempty
model output, and request/response/PTY transcript. Dummy providers stay
supporting evidence only.

### GPU

Aggregate existing backend receipts into rung rows. The aggregate does not
execute a new backend. It stops at the first unavailable rung and preserves
each backend's resume command.

### Physical ARM

Keep the row blocked until a Linux-class ARM board profile is selected.
MCU/QEMU/host compile evidence cannot satisfy Clang/filesystem execution.

## Error codes

Stable design-level reasons:

- `unsupported-schema-major`
- `missing-required-manifest-field`
- `duplicate-evidence-id`
- `unsafe-artifact-path`
- `artifact-root-escape`
- `artifact-not-regular`
- `artifact-size-mismatch`
- `artifact-hash-mismatch`
- `artifact-mime-suffix-mismatch`
- `stale-evidence`
- `unproven-live-status`
- `text-mask-shape-mismatch`
- `text-line-missing`
- `text-line-out-of-order`
- `motion-event-order-invalid`
- `motion-keyframe-invalid`
- `motion-limit-exceeded`
- `protocol-field-range-invalid`
- `protocol-field-value-mismatch`
- `unsafe-html-render-request`

## Performance and observability

No persistent index/cache in v1. Measure direct reads first.

Debug/perf counters:

- manifests read/validated;
- artifacts hashed;
- bytes embedded;
- rows rendered;
- inventory passes;
- elapsed milliseconds.

Targets:

- focused unchanged manifest rendering: median ≤ 1 second;
- full showcase inventory pass: ≤ 10 seconds;
- exactly one inventory pass;
- zero scans/subprocesses in application request/startup paths.

Add a cache only if the focused/full measurements miss these targets.

## Spec-to-SSpec handoff

Later generator work imports the stable schema/requirement mapping, preserves
manual text outside generated markers, uses modern `use std.spec.*` scenarios,
and emits `pending(...)` when no executable oracle exists. It must not emit
boolean-wrapper assertions or evidence claims derived only from prose.

## Planned file impact

### New shared implementation

- `src/lib/common/spec/scenario_text_evidence.spl`
- `src/lib/common/spec/scenario_motion_evidence.spl`
- `src/lib/common/spec/scenario_protocol_evidence.spl`
- `src/lib/nogc_sync_mut/spec/scenario_evidence_manifest.spl`
- `src/app/spipe_docgen/spipe_docgen/evidence_manifest.spl`
- `config/evidence_showcase.sdn`

### Existing implementation owners

- `src/lib/common/spec/scenario_evidence.spl`
- `src/lib/common/spec/scenario_helpers.spl`
- `src/lib/nogc_sync_mut/spec/evidence_receipt.spl`
- canonical pure-Simple runner files
- `src/app/spipe_docgen/spipe_docgen/{common,parser,generator,main}.spl`
- only the selected existing producer/feature owners

### Root/discoverability

- `EVIDENCE_SHOWCASE.md`
- `FILE.md`
- `README.md`
- `config/FILE.md`

### Workflow guidance

- `doc/07_guide/infra/sspec_scenario_manual.md`
- `doc/07_guide/infra/testing.md`
- `doc/07_guide/app/spipe/evidence_showcase.md`
- `doc/07_guide/README.md`
- `test/README.md`
- `doc/06_spec/FILE.md`
- `.codex/skills/{sp_dev,system_test,design}/SKILL.md`
- matching `.agents`, `.claude`, and `.gemini` development surfaces
- `.claude/templates/spipe_template.spl`

The current template/skill examples using `use std.spec` or `Then_*` must be
updated to the selected modern SSpec rule.

## Verification handoff

The implementation is not complete until:

- every REQ/NFR maps to modern executable tests;
- generated manuals have visible primary flows and zero stubs;
- root/subproject rows are receipt-derived;
- all required path/security/media negative tests pass;
- workflow docs and templates agree;
- `doc/06_spec` contains no executable `.spl`;
- environment/runtime facade audits pass; and
- an independent highest-capability review accepts generated-manual quality and
  done marks.

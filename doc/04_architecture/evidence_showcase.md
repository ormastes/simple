<!-- codex-architecture -->
# Architecture: Evidence Showcase and SSpec Evidence Manifests

## Status

Proposed design for the selected evidence-showcase requirements.

## Purpose

Make critical Simple feature claims traceable from a root
`EVIDENCE_SHOWCASE.md` to modern SSpec, a generated manual, a verified evidence
manifest, and retained artifacts or an explicit blocker.

This architecture extends current evidence owners. It does not implement the
separate `Capture` trait/registry proposed in
`doc/05_design/sspec_capture_extension.md`; the selected scope needs a stable
manifest and a few typed helpers, not runtime-extensible capture factories.

## Context

The repository already has:

- capture intent and artifact structures in
  `src/lib/common/spec/scenario_evidence.spl`;
- capture/check helpers in `src/lib/common/spec/scenario_helpers.spl`;
- a pure fail-closed `EvidenceReceipt` in
  `src/lib/nogc_sync_mut/spec/evidence_receipt.spl`;
- SSpec execution in the canonical test runner;
- manual parsing/rendering in
  `src/app/spipe_docgen/spipe_docgen/{parser,generator,main}.spl`;
- structured UI evidence through SGTTI, UI access, Draw IR, and browser/CDP
  surfaces;
- still capture/comparison through the QEMU, Electron, and compositor owners;
  and
- canonical tracked and ephemeral artifact roots.

The missing link is a versioned, runner-written manifest that joins these
surfaces. Today `@capture` mostly describes intent to docgen, evidence paths are
free text, missing artifacts can be silently omitted, and feature claims are
distributed across dated reports.

## Evaluated approaches

| Approach | Decision | Reason |
|---|---|---|
| New capture trait, registry, goldens, and rendering plugins | Reject for this lane | Duplicates existing artifact/helpers and adds runtime composition before any automatic capture path works |
| Scrape `build/`, reports, and generated Markdown | Reject | Full-tree scans, stale files, weak provenance, and false-green status |
| One manifest composed from current artifacts/receipts, consumed by runner/docgen/showcase | Select | Smallest owner-boundary change that provides truth, rendering, and deduplication |

## Architectural decision

### 1. Pure evidence records and manifest trust boundary

Add small pure common modules:

- `src/lib/common/spec/scenario_text_evidence.spl`
- `src/lib/common/spec/scenario_motion_evidence.spl`
- `src/lib/common/spec/scenario_protocol_evidence.spl`

They own:

- `ScenarioTextEvidencePolicy`
- `ScenarioTextMask`
- `ScenarioTextMatchResult`
- `ScenarioMotionEvidence`
- `ScenarioProtocolFieldEvidence`
- `ScenarioArtifactIntegrity`

Add `src/lib/nogc_sync_mut/spec/scenario_evidence_manifest.spl` as the single
trust/promotion boundary. It owns `ScenarioEvidenceManifest`, its SDN codec,
schema validation, status derivation, and composition of the existing
`EvidenceReceipt`, `ScenarioEvidenceArtifact` values, typed detail, and blocker
fields. It does not replace the existing types.

The manifest records:

| Group | Required fields |
|---|---|
| Schema | major/minor version |
| Traceability | feature, requirements, spec path, scenario and step IDs, generated manual path |
| Truth | required/optional, result, showcase status, reason |
| Provenance | source revision/digest, exact command, producer/version, host, target, backend, start/duration |
| Artifacts | kind, MIME, canonical relative path, byte size, checksum, summary, required flag |
| Blocking | prerequisite, exact resume command, owner, final reviewer |
| Typed detail | text policy/result, motion events/keyframes, protocol field rows as applicable |

Unknown minor-version fields are ignored. Unknown major versions, missing
required fields, invalid enum values, and malformed paths fail validation.

### 2. Preserve and adapt `EvidenceReceipt`

`EvidenceReceipt` remains the pure fail-closed execution receipt used by
existing SimpleOS/native gates. Extend its version/status/freshness validation
and add an adapter beside it that maps a verified receipt into a
`ScenarioEvidenceManifest` truth/provenance section.

The adapter preserves the original receipt fields and rules. It must not turn:

- `hosted_fallback` into bare-metal evidence;
- `interpreter_fallback` into native evidence;
- `unsupported` or `blocked` into PASS; or
- an old artifact into current evidence.

Other producers may build the common manifest directly. They do not need a
second receipt class.

### 3. Central constructors, no new capture registry

Extend the constructors in `scenario_evidence.spl` and
`scenario_helpers.spl` so existing producers can add integrity and typed detail.
Direct producer-specific rendering remains outside the common contract.

No global registry, factory, interface-with-one-implementation, or automatic
golden acceptance is introduced. A producer captures with its existing owner,
returns an artifact, and the runner persists the manifest.

### 4. Runner persistence

The canonical SSpec runner writes one manifest per executed scenario/manual
flow under:

`build/test-artifacts/<spec-relative-path>/evidence.sdn`

Rules:

- write a temporary sibling and replace only after complete validation;
- never emit PASS when a required artifact/check is missing;
- preserve bounded stdout/stderr receipts;
- a skipped/unsupported/blocked row is written explicitly, not omitted;
- cached test results may reference a prior manifest only when source,
  producer, target, and artifact digests still match; and
- test execution result and thread/goal status remain separate facts.

### 5. Deterministic docgen lookup

For a focused spec, docgen derives exactly one manifest path from the spec path.
It does not scan `build/` or the repository.

Docgen validates the manifest, reads only declared artifacts beneath:

- `build/test-artifacts/<spec-relative-path>/`; or
- `doc/06_spec/image/<spec-relative-path>/`.

It then renders typed evidence beneath the producing step. A missing required
manifest/artifact is a generation error; optional missing evidence renders a
warning with the declared reason.

### 6. Curated showcase inventory, generated truth

Add `config/evidence_showcase.sdn` as the small curated inventory of critical
rows. It contains titles, categories, requirement/spec/manual paths, optional
subproject showcase links, and display order. It contains no editable PASS
status.

`spipe-docgen --showcase` reads that inventory and each row's deterministic
manifest path, then updates only the generated region in:

- root `EVIDENCE_SHOWCASE.md`; and
- selected subproject `EVIDENCE_SHOWCASE.md` files.

Human introduction/claim-boundary prose stays outside:

```text
<!-- evidence-showcase:generated:start -->
<!-- evidence-showcase:generated:end -->
```

The root file is declared in `FILE.md` and linked from `README.md`.

### 7. Showcase status derivation

The showcase status is derived, never hand-selected:

| Status | Derivation |
|---|---|
| `live-pass` | Current source/producer/target, verified receipt, all required checks/artifacts PASS |
| `historical-pass` | Verified prior PASS whose freshness/current-source policy no longer holds |
| `contract-only` | Executable contract/spec exists but no qualifying live execution receipt |
| `blocked` | Prerequisite absent or latest required execution failed; reason and last result are shown |
| `unsupported` | Target/capability is explicitly unsupported |
| `planned` | Requirement/design exists but no executable contract |

The manifest retains the raw execution result separately, so a latest `FAIL`
displayed as `blocked` still says `latest result: FAIL`; it is not hidden behind
the status label.

## Data flow

```text
feature / QEMU / browser / GPU / LLM producer
                 |
                 v
existing ScenarioEvidenceArtifact + structured checker result
                 |
                 v
canonical SSpec runner
  validate -> compose/adapt EvidenceReceipt -> atomic evidence.sdn
                 |
          +------+------+
          |             |
          v             v
focused spipe-docgen   spipe-docgen --showcase
generated manual      root/subproject generated table region
          |             |
          +------v------+
             user review
```

## Typed evidence

### Text

`check_text_evidence` performs, in order:

1. bounded input check;
2. ANSI removal and CRLF normalization;
3. line split;
4. selected horizontal-whitespace policy;
5. declared typed mask validation and replacement;
6. ordered expected-line matching with bounded gaps; and
7. first-mismatch diagnostic generation.

Raw and normalized transcripts are separate artifacts. Masks validate the
original field shape before replacement. An undeclared changing value remains a
failure.

### Still and motion

Still comparison continues through existing compositor/renderer owners.
Manifest integrity binds the produced pixels to dimensions, backend, baseline,
comparison mode, and checksum.

Motion is a presentation layer over:

- ordered semantic/event receipts;
- at least two verified keyframes; and
- an optional animated WebP or WebM review artifact.

Video bytes are never compared. The event receipt/keyframes decide PASS.

### HTML

The producer uses an existing browser/CDP, Simple Web semantic, or UI-access
surface to assert DOM-visible text, selectors, attributes, status, and headers.
Docgen:

- renders escaped source in a fenced block;
- renders structured checks as a table;
- embeds a safe still when supplied; and
- links the `.html` artifact.

The GitHub-facing manual never injects captured HTML. Optional local preview is
an isolated sandbox and is outside the first rendering baseline.

### Protocol and crypto

`ScenarioProtocolFieldEvidence` describes a field independently from display:

- byte offset and length;
- bit offset and width;
- mask and endianness;
- stable field name;
- actual and expected values;
- pass/fail status;
- importance/severity; and
- note.

The machine assertion checks raw bytes/decoded values. Docgen generates the
field table and safe text/markup highlighting from those typed rows.

## Layering and MDSOC

This is cross-cutting test/documentation behavior across more than three
feature modules, but compiler MDSOC weaving is unnecessary.

- Treat the manifest contract as an opt-in virtual capsule at the
  `nogc_sync_mut.spec` trust boundary, with pure typed records below it in
  `common.spec`.
- Use adapters at producer boundaries.
- Keep filesystem/process operations in runner/docgen owner modules.
- Do not import SGTTI, browser, GPU, QEMU, or runner code into the common
  contract.
- Do not make production app entrypoints depend on evidence code.

The result is build-time/test-time composition, not runtime feature weaving.

## Startup, hot paths, cache, and invalidation

- Production application startup: unchanged.
- Test execution: one manifest serialization after a scenario flow; no
  repository scan.
- Focused docgen: one deterministic manifest read plus declared artifacts.
- Showcase generation: one pass over the small curated inventory.
- No request handler performs scans, media encoding, or subprocess capture.

Invalidation key:

`schema major + source digest + producer digest/version + target/backend identity + artifact digest`

Any change marks the prior row historical or requires regeneration. File mtime
alone is insufficient. Media encoding is performed by the explicit evidence
producer, never by docgen.

## Failure and security boundaries

- Canonicalize and verify relative artifact paths before reading.
- Reject absolute paths, `..`, NUL, unsupported schemes, and root escape.
- Check declared MIME against allowed kind/suffix combinations.
- Escape Markdown tables, alt text, links, and code fences.
- Redact secret-like values before persistence and rendering.
- Bound every embedded text artifact.
- Never follow artifact-provided executable HTML or script.
- Missing required evidence is a failure, not an empty section.
- Atomic manifest writes prevent partial PASS receipts.

## Root and subproject layout

Root rows are grouped by:

1. Operating systems and hardware
2. Web and database
3. UI, WM, and IDE
4. LLM
5. GPU and processing
6. Crypto and protocols
7. Recent feature evidence

Each critical row shows status, claim boundary, target, last verified revision
or date, generated manual, artifact/blocker, and reproduce/resume command.
Subprojects may add detail but must use the same manifest/status contract.

## Spec-to-SSpec boundary

The existing `migrate_spec_to_spl.spl` lane remains independent until the
manifest schema is accepted. Later integration consumes the versioned contract:

- generated code stays inside the existing generated markers;
- manual SSpec outside markers is byte-preserved;
- supported examples emit modern direct assertions and evidence metadata;
- unsupported examples emit `pending(...)`, never a fake PASS; and
- malformed/duplicate markers fail without overwriting the file.

No second Markdown-to-SSpec generator is added.

## Changed documentation contract

Implementation must update:

- `doc/07_guide/infra/sspec_scenario_manual.md`
- `doc/07_guide/app/spipe/` evidence/showcase guidance
- `.codex/skills/sp_dev/SKILL.md`
- `.codex/skills/system_test/SKILL.md`
- matching `.agents`, `.claude`, and `.gemini` SPipe development instructions
- generated/manual specs demonstrating each evidence kind
- root `FILE.md`, `README.md`, and `EVIDENCE_SHOWCASE.md`

## Consequences

### Positive

- One truth contract replaces path guessing and repeated status prose.
- Existing producers and comparison code remain authoritative.
- Users can inspect claims without source tests.
- Unavailable hardware stays visible without false PASS.
- Focused generation has deterministic, bounded work.

### Negative

- Existing evidence producers must populate provenance consistently.
- Old reports remain historical until re-run through the manifest path.
- A schema adapter is needed for the existing SimpleOS receipt.

### Neutral

- Media formats improve presentation but not the machine oracle.
- Subprojects decide which rows are important; the common status rules remain
  fixed.

## References

- `doc/01_research/local/evidence_showcase.md`
- `doc/01_research/domain/evidence_showcase.md`
- `doc/02_requirements/feature/evidence_showcase.md`
- `doc/02_requirements/nfr/evidence_showcase.md`
- `doc/05_design/sspec_capture_extension.md`
- `doc/03_plan/sspec_modernization_plan.md`
- `doc/07_guide/infra/sspec_scenario_manual.md`

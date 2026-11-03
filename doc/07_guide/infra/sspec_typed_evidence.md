# Modern SSpec Typed Evidence

**Status:** The shared contract, format adapters, action trace, manual rendering,
spec-to-SPipe extension, sidecar evidence loader, and docgen renderer wiring are
landed. Runnable reference examples are under
`test/03_system/tools/spipe/examples/`. The four 2026-08-08 red-team comparator
findings have source fixes and regression cases. Process/file capture providers
and live in-process examples also exist; broader provider qualification and the
designed `sspec-maintain evidence` subcommands/profile-completeness surface
remain separate work. This source-status summary is not a fresh runtime PASS.
See §8 for the exact boundary and §8a for the closed findings.
**Design:** `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`
**Plan:** `doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`
**Research:** `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`

## 1. An observation is not an oracle

A screenshot, terminal grid, protocol transcript, byte buffer, or scene graph is an
**observation**. It records what the system did; it does not decide whether that was
correct. A capture that is merely attached to a manual proves only that something was
photographed.

Typed evidence separates the two. The scenario declares, as data: how the observation is
acquired, how it is parsed, which parts matter, what comparison semantics apply, and how
the result is shown to a reader. The comparator then evaluates that declaration
fail-closed, so a capture nobody actually checked cannot report PASS.

## Specification sources to executed evidence

Use this workflow when deriving tests from standards, PDFs, published vectors,
or reference implementations. The same provenance rules apply to non-crypto
protocols, file formats and application contracts.

### Pin the source and write faithful Markdown

Record the publisher, official URL, document identifier, revision/date, retrieval
date, original filename/format and SHA-256. Keep printed page numbers distinct
from PDF page indexes. Record the applicable license or redistribution limits;
retain an authorized local original and extraction provenance. If no official
PDF exists, pin the official TXT/HTML/reference source and say so. A print-to-PDF
copy is a derived artifact, not an official PDF.

Keep a historical PDF's version attached to its requirements. Check the current
publisher revision and errata separately; record supersession or differences
without silently rewriting the historical source. A hash pins bytes, not their
currency, authority, or applicability to the chosen product version.

Markdown should preserve clause meaning, algorithms, byte order, dimensions,
units, equations and rejection conditions. Check extraction/OCR against the
original around tables, formulas and vectors; mark uncertain text. Distinguish
verbatim transcription from a structured summary. Where redistribution is not
permitted, write a cited summary with section/page references and short allowed
quotations, not a replacement copy of the document. Hash derived artifacts too.

### Trace requirements into real tests

Map each applicable clause to a stable `REQ-*` ID, production owner/public API,
independent expected result, executable scenario and mirrored manual. Record
unsupported features and version boundaries explicitly: an API framing rule or
implementation restriction is not automatically a standard's universal rule.
Inspect existing tests before adding cases; extend missing behaviors rather
than duplicating already-covered vectors to increase a case count.

Use published known answers or independently reasoned/produced expected values.
Pin reference implementation/version and fixture hashes when it supplies the
oracle; label such fixtures separately from standard-body vectors. Never derive
the expected value from the same product call, capture, or implementation being
checked. A reference-oracle PASS establishes the oracle exercise, not product
execution or product PASS. Round trips alone cannot prove independent conformance.

Write modern SSpec under `test/`: unit cases exercise owner boundaries and
invalid inputs; integration cases exercise real callers, provider boundaries or
streaming/persistence as applicable; system cases exercise the supported product
flow. Call the actual production APIs and use real assertions with independent
oracles. Keep `step("...")` readable, helpers implemented, and typed evidence
fail-closed on missing fields, parse errors or unmatched selectors. Capturing
bytes or a verdict without checking it is not acceptance evidence. A fixture
or extracted-provider test must retain its narrower proof class.

### Record RED, repair and GREEN separately

For a defect, author the regression first, then execute it against the original
owner and retain the observed behavioral RED. An unavailable runner, unresolved
import or failed build is a blocker, not proof that the intended defect failed.
Repair the production owner and run the same regression to an observed GREEN,
with positive controls and relevant existing cases. Record source revision,
producer/binary hashes, provider/library identity, backend/target, command,
environment, actual scenario counts, exit status and artifact hashes for each run.

| Evidence state | What may be claimed |
|---|---|
| `AUTHORED_UNRUN` | Test source/manual exists; scenario execution is absent. |
| Source reviewed | Named revision and assertions reviewed; no runtime verdict implied. |
| Build/provider fixture executed | Only the recorded build or isolated provider scope; not the complete product route. |
| Actual owner/provider/backend executed | Recorded scenarios and assertions ran on the named owner/provider/backend; verdict applies only to that scope. |
| Observed RED → fix → observed GREEN | Defect regression demonstrated before and after the repair on identified artifacts. |

These are distinct claims, not interchangeable PASS labels. A source-reviewed
fix with unexecuted tests remains TDD-incomplete. If the admitted runtime is
missing, preserve `AUTHORED_UNRUN`/`TEST_BLOCKED`, state the exact blocker and
remaining execution, and do not substitute bootstrap-seed evidence. A deliberate
mutation or fault injection must be labeled with the altered component and
expected failure. It tests oracle sensitivity; it is not the original defect's
RED or additional production branch coverage unless separately measured as such.

### Measure branches and generate the manual

Report covered branch outcomes over total instrumented branch outcomes for
each owner, provider, backend and target. Keep the instrumented source inventory,
including zero-hit branches/files, and the coverage tool/version and artifacts.
State whether a tool measures branches, decisions or conditions; line/function
coverage and passing case counts cannot replace branch coverage. List exclusions
with reasons without silently removing unreachable or unexecuted outcomes from
the denominator. Do not combine a foreign/reference implementation's coverage
with Simple owner coverage. An absent instrumented run is `UNMEASURED`, not 0%
or 100%; a 99% target is met only by the stated measured numerator/denominator.

Run admitted `spipe-docgen` for changed executable specs, require zero stubs,
and review visible intent/steps plus folded executable source. Mirror
`test/<path>_spec.spl` as `doc/06_spec/<path>_spec.md`; executable `.spl` specs
never belong under `doc/06_spec`. Preserve spec and execution-artifact hashes
and the run's proof class. Docgen success is a documentation result, not evidence
that scenarios executed. Label a hand-authored companion as authored, not
docgen-generated, and record its source hash separately from the actual test
execution status and receipts. It may accompany executed tests with genuine run
artifacts; use `AUTHORED_UNRUN` and mark execution artifacts absent only when
execution is absent. Never invent generated provenance. Preserve historical run
statuses and their runtime identities when refreshing prose.

See the [scenario manual guide](sspec_scenario_manual.md),
[native test workflow](testing/native_test_binary_workflow.md), and
[coverage guide](testing/coverage.md) for the existing runner and rendering paths.

## 2. Pipeline and ownership

```text
EvidenceRequest → provider → RawArtifact → format adapter
→ CanonicalEvidence → OracleSpec + comparator → ComparisonResult
→ ManualBlock[] → spipe_docgen → user manual / QA manual
```

| Stage | Owner today |
|---|---|
| Shared records, selectors, oracle modes, manifest, manual blocks | `src/lib/common/spec/evidence/model.spl` |
| Fail-closed evaluation and manual projection | `src/lib/common/spec/evidence/evidence_comparator.spl` |
| Generic Markdown rendering of `ManualBlock`s | `src/lib/common/spec/evidence/manual_render.spl` |
| GUI/TUI action-trace capture model | `src/lib/common/spec/evidence/action_trace.spl` |
| Format adapters (TUI grid, text protocol, binary layout, 2D/3D scene, simulation/stats) | `src/lib/common/spec/evidence/format/*.spl` — see §7a |
| Spec-to-SPipe evidence extension namespace | `src/lib/common/spec/evidence/spipe_extension.spl` |
| Executable behaviour of all of the above | `test/01_unit/lib/common/spec/evidence/*_spec.spl` and `test/03_system/tools/spipe/examples/` |
| `spipe_docgen` evidence sidecar loader + renderer wiring | `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl` and `generator.spl` |
| Process/file capture providers | `format/exec_capture.spl` and `format/file_capture.spl`; broader acquisition and qualification boundaries remain in §8. |
| `sspec-maintain evidence` commands | Separate designed surface — §8. |

The runtime never renders Markdown. Capture and `spipe_docgen` run in separate processes
sharing only files, so a `render_md()` on a runtime object (the shape of the superseded
`doc/05_design/sspec_capture_extension.md:35-42` design) can never be invoked by the
generator. Providers emit generic `ManualBlock` records instead; docgen stays the sole
renderer and can always fall back to a generic rendering of an unknown block.

## 3. Choosing a profile

A profile is an oracle bundle, not a capture kind. One scenario may produce several
artifacts under one profile.

| Surface | Primary oracle | Supplemental |
|---|---|---|
| TUI | semantic node state + terminal cell grid | rendered text projection |
| Native GUI | semantic state + Draw IR geometry | screenshot when visual output is the requirement |
| HTML / web | DOM / ARIA / Draw IR | screenshot |
| CLI / text | exit status, stdout/stderr records, filesystem effects | terminal capture |
| Text protocol | raw frames + grammar-backed field tree | pretty transcript |
| Binary protocol / file / register | raw bytes + layout-bound field tree | hexdump, bit table |
| 2D rendering | Draw IR, geometry, z/clip/style, hit testing | pixel exact or masked diff |
| 3D rendering | asset validation, scene graph, transforms, materials | rendered image under a pinned renderer |
| Simulation | seed, timeline, invariants, KPI tolerances | plots |
| Performance / statistics | sample distribution with declared tolerance | charts |

Capture GUI pixels only when the behaviour is GUI-only, when visual correctness is itself
the requirement, or when configuration asks for it. A screenshot is supplemental evidence
for an ordinary interaction, never the sole oracle.

## 4. Writing checks

Every constructor below is from `model.spl` and is exercised by the spec.

```simple
use std.common.spec.evidence.model.{check_exact, check_full_pattern, check_ignore, check_multiset, check_bind, check_same_as, oracle_spec, canonical_evidence, evidence_node}
use std.common.spec.evidence.evidence_comparator.{compare_evidence}

val spec = oracle_spec(
    "simple-list/1",
    [
        check_exact("response.status", "200"),
        check_full_pattern("response.headers.request-id", "hex:16"),
        check_ignore("response.headers.date", "server clock"),
        check_multiset("response.body.items", ["alpha", "beta"])
    ]
)
val evidence = canonical_evidence(
    "api",
    "simple-list/1",
    [
        evidence_node("response.status", "200"),
        evidence_node("response.headers.request-id", "0123456789abcdef"),
        evidence_node("response.headers.date", "Tue, 21 Oct 2026 00:00:00 GMT"),
        evidence_node("response.body.items", "alpha"),
        evidence_node("response.body.items", "beta")
    ]
)
val result = compare_evidence(evidence, spec)
```

**`check_exact(path, expected)`** — the selected scalar must equal the expected value.

**`check_full_pattern(path, "hex:16")`** — a pattern is a class token (`hex`, `digit`,
`alnum`) plus an exact length or `*`. It is **not a regex and not a substring match**: the
whole selected value must consist of that class, and an explicit length is enforced. A
value merely *containing* the right shape (`id=4C73A91801D58F22`) fails, which is what
stops a truncated or prefixed identifier from passing review.

**`check_ignore(path, reason)`** — the value is displayed in the manual but excluded from
the verdict. The reason is mandatory. An ignore without one is indistinguishable from "we
never looked", and the comparator rejects it.

**`check_multiset(path, items)` / `check_ordered(path, items)`** — repeated fields keep
their multiplicity. Two identical actual values do not satisfy an expectation of one, so a
duplicated protocol field is a failure rather than a coincidence of set comparison. Use
`check_ordered` only when order is part of the contract.

**`check_numeric_tolerance(path, expected, tolerance, reason)`** — a tolerated measurement
records why it may vary, so a widening tolerance is visible in review instead of buried in
a comparison helper.

**`check_bind(path, name)` + `check_same_as(other_path, name)`** — correlation. The first
captures a value under a name; the second requires another field to carry the same value.
Neither side is an expected literal, so a correlation check cannot be satisfied by a
hard-coded transcript.

**`oracle_spec(...)` vs `oracle_spec_open(...)`** — the default is closed: a field the
oracle never mentions fails the capture. Openness must be chosen deliberately, because an
open document silently absorbs new protocol fields nobody decided to accept.

## 5. Fail-closed rules

Each rule exists because its absence produces a green result that describes nothing.
All are implemented in `compare_evidence` and each has a red fixture in the spec.

| Rule | False green it prevents |
|---|---|
| Parse failure fails the capture | An unparsed document yields an empty node set, which satisfies any subset oracle |
| Unresolved selector fails | The check silently verifies nothing |
| Ambiguous selector fails (declared cardinality) | The check verifies a different node than the manual claims |
| Ignore without a reason fails | An unchecked field reads as a reviewed one |
| All-ignore oracle fails | A capture that ignores everything asserts nothing about production |
| Bind-only oracle fails | Correlation values are captured but never compared |
| Non-numeric tolerance fails | Unrelated words both coerce to numeric zero |
| Overflow-safe tolerance fails | Extreme disagreement wraps into a small difference |
| Closed-mode undeclared field fails | New fields enter the contract without anyone deciding |
| Zero positive resolutions fails | A pattern-only oracle reports a clean pass over an empty observation |
| Manifest digests are validated | Placeholder provenance text masquerades as SHA-256 identity |

Expected values may never be derived from the actual observation under test — that is
equality with itself, not verification.

The 2026-08-08 red-team pass found four additional escapes. They are now closed
by `check_is_positive`, numeric-format validation, overflow-safe tolerance, and
`is_sha256_hex`; the regression cases live in
`typed_evidence_oracle_spec.spl`. See §8a and the retained audit at
`doc/08_tracking/audit/modern_sspec_evidence_contract_redteam_2026-08-08.md`.

## 6. Writing steps a reader can follow

Step text describes intent and observable behaviour. Canonical IDs, selectors,
coordinates, revisions, and masks belong in evidence metadata, not the user's workflow.

Good:

```simple
step("Click “Add task”")
step("Type “Ship release” in “Task name”")
step("Verify “Ship release” appears in the task list")
```

Avoid: `step("Click main#add_task at x=127 y=52")`, `step("Call ui_access_act and wait 200 ms")`,
`step("Check that it works")`.

One visible action or one visible verification per step; quote visible labels and values;
capture after a declared stable postcondition, never after a fixed sleep.

## 7. Provenance

`EvidenceManifest` is the receipt that makes a generated manual falsifiable: schema,
evidence and profile ids, spec path and SHA-256, provider id and version, run id,
environment fingerprint, artifact SHA-256, and status. `evidence_manifest_lines` serializes
those fields in a fixed order, so two runs of the same evidence produce byte-identical
manifests and any diff means a real change. `evidence_manifest_is_complete` rejects a
manifest missing its spec hash, provider identity, run id, or artifact hash — without
them a stale manual cannot be told apart from a current one, however green its checks are.

## 7a. Modules landed 2026-08-08

Each format adapter turns a domain-specific artifact into `CanonicalEvidence`
so the single `compare_evidence` in §5 checks it. Adapters do not acquire live
data; docgen separately consumes a validated sidecar and renders Markdown.

| Module | Lane | What it's for |
|---|---|---|
| `format/terminal_grid.spl` | E2 | Cell-accurate model of a rendered terminal frame (grapheme, width, style per cell) and its comparator projection, for TUI scenarios where column/wrap/clip position is itself part of the claim. |
| `action_trace.spl` | E2b | Records a GUI/TUI interaction as a *sequence* of resolved actions (target resolution, before/after state, settle condition) instead of a single final screenshot, so which element was hit and whether the UI actually settled are both checkable. |
| `format/text_protocol.spl` | E3 | Parses an HTTP-like request/response transcript into evidence nodes without either side knowing about sockets or files — exact/ignore/pattern/multiset/order/correlation all resolve against the parsed frame. |
| `format/binary_layout.spl` | E4 | Decodes a fixed-width integer (register, PTE, capability token, wire header) into evidence nodes from a declared `BinaryLayout`, so the manual's byte/bit table cannot drift from the field set the oracle actually checks. Mirrors the real kernel PTE bitfield accessors in `src/os/kernel/types/bitfield.spl`. |
| `format/scene_profile.spl` | E7a | Structural 2D draw-node trees and 3D scene-graph assets (geometry, z-order, materials, transforms) as evidence, because a screenshot can pass while referencing a mesh that doesn't exist or a clipped node sitting on top of the control under test. |
| `format/simulation_profile.spl` | E7b | Simulation-run and performance/statistics evidence (timeline, invariants, KPI tolerances, sample distributions). f64 is banned — all magnitudes are scaled fixed-point `i64`. |
| `manual_render.spl` | E5 | The sole Markdown renderer for the `ManualBlock` vocabulary in `model.spl`; docgen's sidecar loader now calls it in-process. |
| `spipe_extension.spl` | E6 | Defines `SPIPE_EVIDENCE_EXTENSION_NAMESPACE` (`simple.sspec.evidence.v1`), the versioned opaque-payload shape spec-to-spipe importers attach to `SpecLedgerEntry`/`SpecImportManifest` extension fields. Additive only — does not touch the frozen Phase-0 core. |

## 8. Remaining implementation boundary

Lanes are tracked in `doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`.
The evidence contract, adapters, reference examples, and generated-document
sidecar route are real. Missing capabilities are narrower:

| Capability | Lane | Status |
|---|---|---|
| `spipe_docgen` evidence loader + block renderer wiring | E5 | Implemented through `spipe_docgen/evidence_loader.spl`; it reads the adjacent `.evidence.sdn` sidecar and renders `ManualBlock`s. Absence returns no fragment. The loader currently parses but does not gate rendering through `evidence_manifest_is_complete`, so a rendered fragment alone is not accepted provenance. |
| `sspec-maintain evidence <spec> --explain` / `verify-examples` / `scan --profile-completeness` | — | Designed in `doc/05_design/infra/sspec/sspec_maintain_evidence_findings.md`, not implemented. `src/app/sspec_maintain/*.spl` has an unrelated `evidence` field (a scoring dimension name/string in its own finding record) — it does not import the typed-evidence module either. |
| Live capture providers | — | `format/exec_capture.spl` calls the process facade; `format/file_capture.spl` reads through the file facade. Live in-process UI and other examples exist. Their presence does not establish socket/device/GPU coverage or qualification on every runtime. |
| Runnable reference examples | E8 and later live lanes | Present under `test/03_system/tools/spipe/examples/`; distinguish fixture adapters from `live_*` scenarios and inspect each scenario's actual owner/provider. Headless scene state is not GPU readback or physical display proof. |

The feature expert's retained 2026-08-09 ledger reports process/file and live
example execution on a disclosed Rust seed, with self-hosted requalification
still owed. This guide corrects stale claims that those providers are absent;
it does not upgrade those historical results to current admitted runtime PASS.

## 8a. Closed comparator gaps from red-team review

`doc/08_tracking/audit/modern_sspec_evidence_contract_redteam_2026-08-08.md`
(Wave-0 lane E1) attacked `evidence_comparator.spl` and found four false-green
defects. Current source closes all four:

| Finding | Original defect | Current closure |
|---|---|---|
| F1 (blocker) | Bind-only oracle passes vacuously. | Binds do not count as positive checks; bind-only comparison fails. |
| F2 (blocker) | Non-numeric tolerance coerces garbage to zero. | Both operands require valid signed-decimal text before conversion. |
| F3 (major) | Extreme tolerance subtraction overflows. | `within_tolerance` spends the budget without wrapping subtraction. |
| F4 (major) | Placeholder digest text passes provenance completeness. | `is_sha256_hex` requires exactly 64 hexadecimal characters. |

The retained audit remains the rationale. Current regression cases exercise
each closure; downstream adoption must still retain independent expected values
and real provider provenance.

## 9. Running the coverage

```bash
bin/simple run test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl
```

Use `run` rather than `test` only when the admitted runtime's documented module
cap requires it. The current source contains 28 examples, including all four
red-team closures. Record a fresh pure-Simple verdict before claiming them
executed; the actor/process lane's deployed Stage-4 ABI probe is currently
blocked and supplies no such verdict.

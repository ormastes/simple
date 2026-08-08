# Modern SSpec Completion: Typed Evidence, Executable Manuals, and Spec-to-SPipe Integration

**Audit date:** 2026-08-08
**Status:** Research (revised design + implementation plan extracted to sibling design/plan docs)
**Companion docs:**
- Design: `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`
- Plan: `doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`

---

## 1. Executive decision

Modern SSpec should no longer be defined only as "manual-first scenarios with steps and captures." The completed definition:

> **Modern SSpec is a manual-first, executable, source-mapped behavioral specification whose production observations are converted into typed evidence, evaluated by explicit non-vacuous oracles, and projected into user and QA manuals from the same run.**

The current modernization documents have the correct goals — TUI grids, GUI images, protocol JSON/binary, bit tables, statistics, audience modes, goldens, and traceability — but the proposed `Capture` abstraction is too monolithic. It combines acquisition, parsing, comparison, serialization, and Markdown rendering in one object. This creates an architectural contradiction because the runtime capture object and `spipe_docgen` execute in different processes, while the sidecar does not contain enough structured rendering information for a custom `render_md()` implementation to work.

Replace that model with a staged evidence pipeline:

```text
User action → Action trace → Capture provider → Raw artifact
→ Format parser + normalizer → Canonical evidence
→ Typed oracle comparator → Comparison result
→ Generic manual projection → user manual / QA manual
```

This is not a second test framework. Normal SSpec `describe`/`context`/`it`/`step`/`expect` remains the executable surface. The new layer supplies production observations and domain-specific oracles inside ordinary scenarios.

Three reference examples become mandatory and executable:

1. **Interactive surface:** shared TUI/GUI workflow with click, typing, key press, semantic state, TUI cell capture, conditional GUI capture.
2. **Textual network protocol:** real request/response transcript, grammar-backed parsing, explicit important/ignored/pattern fields, expected/actual structural diff, generated protocol manual.
3. **Binary layout:** raw bytes plus decoded field table, hex and `0b...` forms, byte/bit endian declarations, bound to an actual production struct/register/accessor implementation.

The skill should contain three concise examples. The guide should contain the three complete examples. Their user and QA manuals must be generated from runnable specifications and protected by source-hash/regeneration gates.

---

## 2. Repository audit

### 2.1 What already exists and should be reused

- Manual-first SSpec conventions: triple-quoted narrative, outcome-oriented scenarios, literal `step("...")`, capture metadata, generated Markdown.
- `ScenarioEvidence` and capture metadata categories for TUI, GUI, HTML, API, protocol, text, exec, binary, log, artifacts.
- `ui_access` as the canonical semantic UI inspection/action protocol.
- SGTTI adapters for TUI state, Simple UI, host WM, compositor, hidden/headless GUI, Draw IR.
- `SgttiTestDriver` operations for click, type, visibility, focus, enabled/selected state, text, geometry, style, hit-rectangle assertions.
- `wm_compare` exact pixel comparison and golden gates.
- `spipe_docgen` support for embedded media and TUI text evidence.
- `sspec-maintain` scan, improve, scaffold, documentize, deterministic scoring, anti-vacuity rules.
- The lossless `spec-to-spipe` architecture: immutable source snapshots, byte spans, exact disposition, semantic identity, deterministic manifests, verification, extension namespaces.

These are the correct owners. The modernization should connect them, not introduce parallel GUI automation, protocol parsing, binary layout, manual rendering, or source mapping.

### 2.2 Confirmed gaps

**TUI.** The current path exposes semantic nodes through `ui_access`/SGTTI. A literal rendered terminal-cell snapshot and a component-scoped cell diff are missing as first-class reusable evidence. A robust TUI oracle also needs: terminal rows/columns; cursor position/visibility/shape; grapheme clusters (not code points); cell width and continuation cells; fg/bg and attributes where style is required; width policy, locale, Unicode version, tab width, ambiguous-width policy; semantic node/region identity for scoped comparison.

**GUI.** Semantic action/layout inspection and pixel comparison exist. Missing: a single scenario-level evidence profile coordinating before/action/after semantic snapshots, resolved target and actual dispatched action, settling criteria, Draw IR/SGTTI state and geometry, optional screenshot + pixel comparison, generated manual projection. Screenshot comparison stays supplemental for ordinary interactions; it is a primary oracle only when visual output itself is the requirement.

**Text comparison.** The existing snapshot comparator trims both texts, performs exact equality, then a simple line-by-line diff (despite describing itself as simplified Myers). It does not parse structure, bind selectors, distinguish important vs volatile data, enforce multiplicity/order, or support field-scoped patterns.

**Protocol evidence.** The current evidence record is descriptive: kind, title, MIME type, path/body, scenario/step IDs, redaction. It does not define framing, grammar, canonicalization, correlation, selectors, compare modes, or expected/actual structural results. Protocol unit tests frequently use substring checks over constructed JSON strings — not a sufficient system-test conformance oracle.

**Binary evidence.** `bit_table` / `protocol_binary` plans lack a production-layout binding. A hand-written table can drift from the encoder, decoder, register accessor, ABI struct, or imported standard. Evidence this matters:
- `src/os/kernel/types/bitfield.spl` manually defines actual PTE, capability-token, and PCI register accessors.
- SMF implementation and SMF documentation have tracked layout/version disagreements.
- `#[repr(C)]` structs have target-ABI layout concerns not safely inferable from prose.

**Example integrity.** Several polished example manuals name specification files that did not resolve during this audit. The bare-metal/network example describes CQE, register, and NVMe/TCP evidence while the available named source focuses on NAND CLI output and hand-written text captures. These documents must be labeled design mockups until runnable source, retained artifacts, and regeneration checks exist.

---

## 3. Updated architecture

### 3.1 Core principle: observation is not an oracle

A screenshot, terminal grid, protocol transcript, byte buffer, scene graph, or simulation trace is an **observation**. The scenario must separately declare: acquisition, parsing, normalization of unstable representation, which parts are important, comparison semantics, and reader projection.

### 3.2 Canonical pipeline

```text
SSpec scenario
 ├─ narrative and step text
 ├─ production action driver
 ├─ assertions
 └─ EvidenceRequest
       ↓
EvidenceProvider → RawArtifact → FormatAdapter → CanonicalEvidence
       ↓
OracleSpec + Comparator → ComparisonResult → EvidenceManifest
       ↓
spipe_docgen generic renderer → user manual / QA manual
```

### 3.3 Proposed common records (target API shape)

```simple
struct EvidenceRequest:
    evidence_id: text
    profile_id: text
    target: EvidenceTarget
    oracle: OracleSpec
    audiences: [EvidenceAudience]

struct RawArtifact:
    media_type: text
    bytes: [u8]
    captured_at: text
    provider_id: text
    provider_version: text
    environment: [EvidenceProperty]

struct CanonicalEvidence:
    kind: text
    root: EvidenceNode
    source_map: [EvidenceSourceMap]
    extensions: [EvidenceExtension]

struct ComparisonResult:
    status: EvidenceStatus
    summary: text
    checks: [EvidenceCheckResult]
    diff_artifacts: [EvidenceArtifactRef]

struct ManualProjection:
    blocks: [ManualBlock]
```

`ManualBlock` is a generic structured union: paragraph; ordered action list; code block; terminal grid; image; table; field tree; byte table; expected/actual diff; warning; troubleshooting row; artifact link.

Do **not** put arbitrary provider-owned Markdown rendering code in `spipe_docgen`. A custom provider emits generic `ManualBlock` records or extension data. The doc generator remains the sole Markdown renderer with a generic fallback.

### 3.4 Split registries

```text
EvidenceProviderRegistry   capture live data
FormatAdapterRegistry      parse and normalize
ComparatorRegistry         evaluate typed oracles
ProjectionRegistry         map canonical kinds to generic manual blocks
```

Each stage is independently testable; one parser/comparator is reused by hand-written SSpec, spec-to-spipe generated SSpec, CLI/API inspection tools, generated manuals, semantic diff, and imported register/protocol definitions.

### 3.5 Typed selectors

```simple
enum EvidenceSelector:
    CanonicalNode(id: text)
    ProtocolField(path: text)
    JsonPointer(pointer: text)
    XmlPath(path: text)
    RecordField(record: text, field: text, occurrence: i64)
    TerminalRegion(node_id: text)
    PixelRegion(rect: Rect)
    ByteRange(offset: i64, length: i64)
    BitRange(lsb: i64, width: i64)
    BinaryField(path: text)
    ScenePath(path: text)
    SimulationSignal(path: text)
```

Every selector must resolve to exactly the declared cardinality. Missing or ambiguous selectors fail unless explicitly optional.

### 3.6 Oracle checks

```simple
enum OracleMode:
    Exact
    Semantic
    Subset
    OrderedSequence
    Multiset
    FullPattern
    NumericTolerance
    ImageExact
    ImageThreshold
    Invariant
    Timeline
    Distribution
    Ignore
```

Each check records selector, mode, typed expected value, optional tolerance/pattern, required cardinality, order/multiplicity policy, reason for ignore/tolerance, and source requirement ID.

Fail-closed rules:
- parse failure fails; unresolved selector fails; ambiguous selector fails;
- pattern matching is full-value by default, not substring;
- an ignore requires a reason;
- pattern-only mode with zero resolved checks fails;
- closed-document mode rejects unexpected nonignored fields;
- each important field must be checked exactly once;
- an observation without at least one positive production oracle cannot pass;
- expected values may not be derived from the actual observation under test.

---

## 4. Interactive TUI/GUI reference profile

### 4.1 Surface-selection policy (`SurfacePolicy.Auto`)

| Product surface | Default evidence |
|---|---|
| TUI | semantic SGTTI snapshot + rendered terminal-cell snapshot |
| HTML/web | semantic/ARIA/DOM or Draw IR; screenshot supplemental |
| Native GUI | semantic SGTTI/Draw IR; screenshot when visual behavior is required |
| Shared TUI+GUI feature | one semantic action script on both; parity comparison |
| GUI-only feature | GUI capture enabled automatically |
| Explicit configuration | honor `capture.gui=true` or equivalent metadata |
| 2D/3D visual feature | scene/Draw IR plus configured pixel oracle |

Do not capture GUI merely because a GUI backend exists. Existing `wm_compare` exact lanes are not weakened; named profiles: `pixel_exact`, `pixel_masked_exact`, `pixel_threshold` (explicitly approved, environment-fingerprinted, bounded), `pixel_diagnostic` (never turns semantic failure into pass).

### 4.2 Action trace

Every interaction records: before snapshot, resolved target, requested action, actual dispatched action, input payload, action-time snapshot, after snapshot, settle condition + duration/iterations, resulting revision. Vocabulary: click/double click, type/paste, press key/chord, focus, select/toggle, drag, scroll, resize, invoke/submit. Canonical ID + role + visible name preferred; coordinates are a fallback that must record which node was actually hit.

No fixed sleeps. Settle on a bounded observable condition: expected node/state exists; UI revision stops changing for N polls; animation-idle; pending event/action queue empty; expected Draw IR batch/compositor frame committed.

### 4.3 TUI cell model

```simple
struct TerminalSnapshot:
    columns: i64
    rows: i64
    cells: [TerminalCell]
    cursor: TerminalCursor
    width_profile: TerminalWidthProfile
    semantic_regions: [TerminalRegion]

struct TerminalCell:
    grapheme: text
    display_width: i64
    continuation: bool
    foreground: TerminalColor
    background: TerminalColor
    attributes: TerminalAttributes
    semantic_id: text
```

Comparison profiles: `tui_text_exact` (grapheme + display width); `tui_text_style` (+ colors/attributes); `tui_scoped` (only regions resolved from canonical node IDs); `tui_masked` (all except declared volatile regions); `tui_semantic_and_grid` (required default for interactive system tests).

Store both a canonical `.tui.sdn` artifact (cells/styles/regions) and a human-readable `.txt` projection. Never compare raw ANSI escape streams as the primary golden. Grapheme clusters, not code points; terminal width needs an explicitly pinned policy (East Asian width is not an off-the-shelf terminal-width algorithm).

Mandatory Unicode fixtures: combining sequence; emoji/variation sequence; East Asian wide char; ambiguous-width char under two declared profiles; ZWJ sequence; clipped double-width char at terminal edge.

### 4.4 Manual wording rules

Good:
```simple
step("Click “Add task”")
step("Type “Ship release” in “Task name”")
step("Press Enter")
step("Verify “Ship release” appears in the task list")
```
Avoid: `step("Click main#add_task at x=127 y=52")`, `step("Call ui_access_act and wait 200 ms")`, `step("Check that it works")`.

Rules: one visible action or verification per `step`; quote visible labels/values; imperative language; canonical IDs/selectors/coordinates/revisions/masks live in evidence metadata; capture after a declared stable postcondition; mention terminal dimensions only when behavior depends on them; user manual shows approved behavior + capture; QA manual additionally shows target resolution, expected/actual, masks, environment, diff.

### 4.5 Proposed executable example (target API)

```simple
# Proposed target API
use std.spec
use std.ui_test
use std.spec.evidence

# @manual_section Adding a task
# @user_facing
# @req REQ-TODO-ADD-001
# @surface auto

describe "Todo task entry":
    """
    Add a task through the same operator workflow on the configured TUI or GUI
    surface. The task must remain visible after submission.
    """

    it "adds a task and displays it in the task list":
        val app = launch_todo_system_fixture()
        val ui = ui_test_driver(app, configured_ui_target())

        step("Click “Add task”")
        expect(ui.click("main#add_task")?).to_equal(true)

        step("Type “Ship release” in “Task name”")
        expect(ui.type_text("main#task_name", "Ship release")?).to_equal(true)

        step("Press Enter")
        expect(ui.press("main#task_name", "Enter")?).to_equal(true)

        step("Verify “Ship release” appears in the task list")
        expect(ui.check_text("main#task_list", "Ship release")?).to_equal(true)

        expect_evidence(
            capture_surface(ui, "task-added"),
            interactive_surface_oracle(
                semantic_ids: ["main#task_list", "main#task_name"],
                tui_grid: scoped(["main#task_list", "main#task_name"]),
                gui_image: when_gui_only_or_configured(),
                pixel: exact_or_configured_profile()
            )
        )
```

The system fixture must launch the production command/backend. The driver must not fabricate state transitions.

QA evidence table shape:

| Check | Expected | Actual | Result |
|---|---|---|---|
| `main#task_list` text | contains `Ship release` | contains `Ship release` | PASS |
| TUI region | approved cell grid | 0 differing cells | PASS |
| TUI/GUI parity | visible/enabled/selected equal | equal | PASS |
| GUI pixels | exact/configured profile | hash + diff summary | PASS or N/A |

---

## 5. Textual network reference profile

### 5.1 Documentation pattern

Generated manual layers (modeled on RFC 9112 / AsyncAPI presentation): purpose/direction; framing + charset; formal grammar (ABNF); message anatomy/field table; annotated request/response example; expected/actual verification table; malformed/error examples; retained raw transcript in QA appendix.

### 5.2 One protocol-trace envelope for text and binary

```simple
struct ProtocolTrace:
    transport: text
    connection_id: text
    frames: [ProtocolFrame]

struct ProtocolFrame:
    sequence: i64
    direction: ProtocolDirection
    correlation_id: text
    captured_at: text
    payload: ProtocolPayload

enum ProtocolPayload:
    Text(raw: [u8], profile_id: text)
    Binary(raw: [u8], layout_id: text)
    Structured(value: EvidenceNode, media_type: text)
```

Binary network traffic is a `ProtocolFrame` with the binary-layout adapter, not a parallel framework.

### 5.3 Text format profile

```simple
struct TextFormatProfile:
    profile_id: text
    charset: text
    framing: TextFraming
    grammar_ref: GrammarRef
    record_model: text
    canonicalizers: [TextCanonicalizer]
    openness: DocumentOpenness
```

Built-in adapters: raw line protocol; ABNF-described; HTTP-like message; JSON; XML; YAML; CSV/TSV; key/value log; compiler diagnostic; CLI transcript.

### 5.4 Comparison semantics

```simple
exact("response.status", 200)
full_pattern("response.headers.request-id", hex_digits(16))
ignore("response.headers.date", reason: "server clock")
multiset("response.body.items", ["alpha", "beta"])
bind("request.headers.correlation-id", "request_id")
same_as("response.headers.correlation-id", "request_id")
```

Rules: pattern applies to a selected scalar, anchored/full-value by default, never globally; "ignore" = display but exclude from verdict; field order normalized only when the protocol declares it insignificant; duplicate fields preserve multiplicity; parse failure is a test failure; raw bytes remain retained; closed mode rejects undeclared extra fields (open mode must be explicit); pattern-only with zero selector resolutions is a blocker. JSON uses JSON Pointer (RFC 6901) or another typed path; manuals show pretty JSON, not canonical one-line form.

### 5.5 Example wire protocol + scenario

```abnf
request        = command SP path CRLF
                 accept-line
                 correlation-line
                 CRLF
command        = %s"LIST"
path           = "/" 1*(ALPHA / DIGIT / "-" / "_")
accept-line    = %s"Accept:" SP media-type CRLF
correlation-line = %s"Correlation-Id:" SP 16HEXDIG CRLF
response       = status-line
                 request-id-line
                 date-line
                 count-line
                 CRLF
                 *item-line
status-line    = 3DIGIT SP reason CRLF
item-line      = 1*(ALPHA / DIGIT / "-" / "_") CRLF
```

```simple
# Proposed target API
describe "Simple List protocol":
    """
    A client requests the current project names. The server returns a success
    status and one line per project.
    """

    it "returns the project list and preserves request correlation":
        val server = launch_production_list_server()
        val client = production_list_client(server.endpoint())

        step("Request the project list")
        val trace = capture_protocol("list-projects"):
            client.list_projects("/projects")

        step("Verify the server returns the available projects")
        expect_protocol(
            trace,
            protocol_oracle(
                exact("request.command", "LIST"),
                exact("request.path", "/projects"),
                exact("response.status", 200),
                full_pattern("response.headers.request-id", hex_digits(16)),
                ignore("response.headers.date", "server clock"),
                multiset("response.body.items", ["alpha", "beta"]),
                same_as(
                    "response.headers.correlation-id",
                    "request.headers.correlation-id"
                )
            )
        )
```

Generated QA verification table:

| Selector | Mode | Expected | Actual | Result |
|---|---|---|---|---|
| `request.command` | exact | `LIST` | `LIST` | PASS |
| `response.status` | exact | `200` | `200` | PASS |
| `response.headers.request-id` | full pattern | 16 hex digits | `4C73A91801D58F22` | PASS |
| `response.headers.date` | ignore | server-clock field | retained raw value | IGNORED |
| `response.body.items` | multiset | `alpha`, `beta` | `beta`, `alpha` | PASS |
| correlation binding | same value | request ID | same response ID | PASS |

A failed field shows frame + direction, raw lines around the source span, parsed selector, expected/actual typed values, structural diff, parser/profile versions. CBOR/CDDL (RFC 8949/8610) model the binary-side separation of interchange bytes vs diagnostic notation.

---

## 6. Binary-layout reference profile

### 6.1 Binary evidence model

```simple
struct BinaryEvidence:
    raw: [u8]
    byte_order: ByteOrder
    bit_order: BitOrder
    base_offset: i64
    layout_ref: BinaryLayoutRef
    decoded: BinaryFieldNode
```

Table projection: `| Offset | Bytes | Bits | Field | Raw hex | Raw binary | Decoded | Expected | Result |`.

Rules: always state byte endian and bit numbering; `0x...` / `0b...` with underscore grouping; byte offsets and bit ranges kept separate; field-level masks over anonymous byte wildcards; reserved fields represented and tested; raw + decoded both retained; the manual table is generated from the same layout used by the parser/comparator.

### 6.2 Layout-source adapters (one `BinaryLayoutIR`)

1. **Compiler/ABI struct layout** — actual offsets/sizes/alignment/triple/packing from compiler metadata, never source-text inference.
2. **RegisterIR** — imported by spec-to-spipe from CMSIS-SVD, vendor XML, tables, prose overlays; width, bit ranges, access semantics, reset value, enums, constraints, source spans.
3. **AccessorLayoutAdapter** — bridges existing production `bits_get`/`bits_set`, PTE, capability token, PCI, NVMe accessors (transitional).
4. **External declarative schema** — Kaitai Struct, CDDL, protobuf/IDL, packet dissector fields, or a repo-native layout description.

### 6.3 Required binary oracles

Total size/alignment; field offset/width; byte endian; bit numbering; decode known bytes; encode known values; round trip; one-hot field isolation; adjacent-field preservation; reserved-bit zero/preserve policy; enum validity; length/count constraints; checksum where applicable; malformed/truncated input; production encoder/decoder/accessor path exercised.

### 6.4 Actual PTE integration example

`src/os/kernel/types/bitfield.spl` production layout: bit 0 present; bit 1 writable; bit 2 user; bits 51:12 physical address; bit 63 no-execute.

```simple
# Proposed target API
describe "x86_64 page-table entry":
    """
    A writable supervisor page is encoded with a 4 KiB-aligned physical
    address and the no-execute protection bit.
    """

    it "encodes and decodes the production PTE accessors":
        val pte = pte_make(
            phys_addr: 0x0000_0000_1234_5000,
            present: true,
            writable: true,
            user: false,
            no_execute: true
        )

        step("Encode the page-table entry")
        val evidence = capture_u64_le("kernel-pte", pte, layout: pte_accessor_layout())

        step("Verify the page address and protection flags")
        expect_binary(
            evidence,
            binary_oracle(
                exact_field("present", true),
                exact_field("writable", true),
                exact_field("user", false),
                exact_field("physical_address", 0x0000_0000_1234_5000),
                exact_field("no_execute", true),
                exact_reserved("reserved", 0)
            )
        )

        expect(pte_get_phys_addr(pte)).to_equal(0x0000_0000_1234_5000)
        expect(pte_get_present(pte)).to_equal(true)
        expect(pte_get_writable(pte)).to_equal(true)
        expect(pte_get_user(pte)).to_equal(false)
        expect(pte_get_no_execute(pte)).to_equal(true)
```

Expected value:
```text
u64:   0x8000_0000_1234_5003
LE bytes: 03 50 34 12 00 00 00 80
binary: 0b10000000_00000000_00000000_00000000_00010010_00110100_01010000_00000011
```

| Offset | Bytes | Bits | Field | Raw | Decoded | Expected | Result |
|---:|---|---|---|---|---|---|---|
| `0x00` | `03` | `[0]` | present | `0b1` | `true` | `true` | PASS |
| `0x00` | `03` | `[1]` | writable | `0b1` | `true` | `true` | PASS |
| `0x00` | `03` | `[2]` | user | `0b0` | `false` | `false` | PASS |
| `0x01..0x06` | `50 34 12 00 00 00` | `[51:12]` | physical address | `0x0000_0000_1234_5000` | aligned address | same | PASS |
| `0x07` | `80` | `[63]` | no-execute | `0b1` | `true` | `true` | PASS |

A deliberate-red fixture flips exactly one bit and must identify the field, bit range, expected, actual, affected byte.

### 6.5 Struct-layout caveat

For `repr(C)`/ABI structures the adapter must bind compiled target triple, actual size/alignment, compiler-reported offsets, packing attributes, endian conversion path, source type identity + hash. Especially important for SMF until doc/impl versions synchronize.

---

## 7. Missing category profiles

A profile selects an oracle bundle; a category is not a capture kind.

| Profile | Primary evidence | Supplemental |
|---|---|---|
| Interactive surface | semantic action/state + TUI grid or Draw IR | screenshot, accessibility tree |
| CLI/text | exit, stdout/stderr records, filesystem effects | terminal capture |
| Text protocol | raw frames + grammar-backed field tree | pretty transcript |
| Binary protocol/file/register | raw bytes + BinaryLayoutIR field tree | hexdump, bit table |
| Structured API/data | schema validation + selected semantic fields | pretty JSON/XML/YAML |
| Compiler/language | AST/IR/diagnostics/runtime result | source excerpts, traces |
| Filesystem/database | state transition, transaction, durability | query plan, file diff |
| Concurrency/distributed | event history, happens-before/invariants | timeline diagram |
| 2D rendering | Draw IR, geometry, z/clip/style, hit testing | pixel exact/masked diff |
| 3D rendering/assets | scene graph, transforms, materials, asset validation | rendered images |
| Simulation/control/physics | model validation, seed, timeline, invariants, KPIs | plots/video |
| Audio/media/signal | samples/features, duration, RMS/spectrum | waveform/spectrogram |
| Performance/statistics | samples, distribution, confidence/tolerance | charts |
| ML/probabilistic | dataset/model hash, seed, metrics/distribution | examples |
| Hardware/RTL/formal | interface/register trace, assertions, proof artifacts | waveforms |
| Security/fuzz/recovery | corpus, invariant, crash/recovery evidence | minimized input/log |

3D: validate assets structurally (glTF-validator model — JSON/GLB structure, references, accessors, animation, images, extensions) before any rendered-screenshot oracle. Simulation: do not assume exact cross-simulator trajectories (ASAM OpenSCENARIO explicitly disclaims it); record model version, seed, solver/time-step, events, invariants, KPIs, tolerances, termination, environment.

---

## 8. `spec-to-spipe` consistency

- The v1 `SpecImportManifest` core is frozen; add evidence via a versioned extension namespace `simple.sspec.evidence.v1`. Do not reopen source identity or byte-disposition core; propose core v2 only if evidence genuinely cannot stay additive.
- New semantic nodes (each with stable ID, source span, requirement binding, adapter rule ID, provenance, disposition, extensions): `InteractionCase`, `ActionStep`, `EvidenceProfileRef`, `EvidenceOracle`, `EvidenceSelector`, `ProtocolGrammarRef`, `BinaryLayoutRef`, `ComparisonCheck`, `ManualProjectionHint`.
- Importer mapping: OpenAPI → structured API profile; AsyncAPI → message/channel/protocol trace; RFCXML+ABNF → textual protocol grammar; CDDL → CBOR binary profile; Kaitai → binary layout; CMSIS-SVD → RegisterIR; WPT/HTML/ARIA → interactive/web profile; Khronos XML/CTS → API/asset/rendering; OpenSCENARIO/FMI → simulation.
- One import deterministically emits: generated `*_spec.spl`; evidence profile/manifest; source map + disposition ledger; QA manual; user/operator manual where applicable; semantic-diff baseline. Generated SSpec is immutable; hand-written overlays stay separate and source-mapped.
- `spec-to-sspec` remains a compatibility alias; do not advertise the external-standard CLI as production-ready before the executable command and gates land.

---

## 9. Tool plan

Reuse: `simple test <spec>`; `simple sspec-maintain scan|documentize <spec>`.

Proposed additions:
```text
simple sspec-maintain evidence <spec> --explain
simple sspec-maintain verify-examples
simple sspec-maintain scan <spec> --profile-completeness
simple test <spec> --update-evidence
simple test <spec> --accept-evidence
```
New/changed evidence stays `pending-review` until accepted.

New maintenance findings:

| Rule | Finding |
|---|---|
| `SSDOC-EVD-101` | untyped/free-form evidence where a profile exists |
| `SSDOC-EVD-102` | selector missing or ambiguous |
| `SSDOC-EVD-103` | ignored value has no reason |
| `SSDOC-EVD-104` | pattern-only oracle resolves zero checks |
| `SSDOC-EVD-105` | claimed generated example has no runnable source |
| `SSDOC-EVD-106` | source/profile/provider hash stale |
| `SSDOC-EVD-107` | capture has no positive production oracle |
| `SSDOC-UI-101` | interaction verified only by screenshot |
| `SSDOC-UI-102` | fixed sleep instead of bounded settling |
| `SSDOC-TUI-101` | TUI golden lacks width/terminal profile |
| `SSDOC-PROTO-101` | parsed comparison has no retained raw transcript |
| `SSDOC-PROTO-102` | global regex used instead of selected field pattern |
| `SSDOC-BIN-101` | binary table not bound to production layout |
| `SSDOC-BIN-102` | byte endian or bit numbering unspecified |
| `SSDOC-MAN-101` | manual edited independently from generated source |

Example-integrity receipt per generated manual: spec path; spec SHA-256; evidence manifest schema/version; provider/parser/comparator IDs+versions; run ID; environment fingerprint; golden/artifact hashes; generator identity/version; generated-at or reproducible-build identity. Human manual shows a concise subset; sidecar retains the full receipt.

---

## 10. Acceptance gates

**Common:** three reference specs exist and execute; user + QA manuals regenerate byte-identically under pinned environment; source path + SHA-256 match; missing source / stale hash / missing artifact / unaccepted golden / parser error / unknown profile fails; every oracle has a deliberate-red fixture; existing capture APIs work through compatibility adapters; existing exact `wm_compare` gates retain exact semantics.

**Interactive surface:** click/type/press in the action trace; before/action/after target resolution retained; semantic result asserted; TUI cell grid captured + compared; scoped diff ignores only declared regions; GUI capture obeys auto/gui-only/configured policy; shared TUI/GUI scenario proves parity; Unicode wide/combining/emoji covered; one-cell and one-style deliberate regressions produce useful diffs.

**Text protocol:** valid + malformed grammar fixtures; exact/subset/ordered/multiset/pattern/ignore/correlation checks; duplicate-field multiplicity; closed-mode extra-field failure; unresolved-pattern-selector failure; raw + canonical views retained; expected/actual table generated; direction + frame sequence preserved.

**Binary:** actual PTE production accessors; layout width/ranges/endian declared; decode/encode/round trip; one-hot mutation; adjacent-field preservation; reserved-bit policy; LE + BE fixtures; truncated/invalid input; table generated from the same layout as comparison.

**spec-to-spipe:** evidence nodes carry existing stable IDs + spans; extensions survive deterministic round trip; 100% source disposition; generated SSpec/manifest/manual/ledger agree; no tautological generated assertion; unresolved oracle fails fast; `spec-to-sspec` alias parity once the production CLI lands.

---

## 11. Recommended immediate order

1. Freeze `EvidenceManifest v1`, typed selectors, checks, result, `ManualBlock`.
2. Add the deliberate-red verifier before implementing providers.
3. Implement textual comparator + PTE binary adapter first (deterministic, no GUI variability).
4. Add TUI cell capture + SGTTI-region mapping.
5. Add GUI action-trace + `wm_compare` adapter without changing current exact gates.
6. Implement generic docgen projection.
7. Land the three executable examples; delete or relabel non-generated mockups.
8. Add spec-to-spipe extension/emitter integration.
9. Add 2D/3D/simulation profiles.
10. Migrate legacy evidence incrementally behind compatibility wrappers.
11. Update all skills/templates/guides in the same change that makes the workflow executable.
12. Run independent deliberate-red + freshness review before claiming Modern SSpec complete.

---

## 12. Research basis

**Repository sources inspected:**
`doc/02_requirements/feature/sspec_scenario_manual.md`; `doc/03_plan/sspec_modernization_plan.md`; `doc/05_design/sspec_capture_extension.md`; `doc/07_guide/infra/sspec_scenario_manual.md`; `doc/07_guide/infra/sspec_documentization_maintenance.md`; `.claude/skills/spipe.md`; `.claude/agents/spipe/spec.md`; `src/lib/common/spec/scenario_evidence.spl`; `src/lib/nogc_sync_mut/ui_test/sgtti.spl`; `doc/07_guide/app/ui/ui_access.md`; `src/app/wm_compare/golden_gate.spl`; `src/app/wm_compare/backend_parity.spl`; `src/compiler_rust/lib/std/src/spec/snapshot/comparison.spl`; `src/os/kernel/types/bitfield.spl`; `src/compiler_rust/common/src/smf/header.rs`; `doc/04_architecture/format/smf_implementation_status.md`; `doc/04_architecture/app/spec_to_spipe.md`; `doc/05_design/app/spec_to_spipe_ir.md`; `doc/03_plan/agent_tasks/spec_to_spipe.md`; `doc/07_guide/app/spipe/manual_examples/`.

**External standards/tools:** Playwright visual comparisons + ARIA snapshots; Textual headless testing/Pilot; Unicode Text Segmentation + East Asian Width; RFC 9112 (HTTP/1.1); RFC 5234 (ABNF); RFC 6901 (JSON Pointer); RFC 8949 (CBOR diagnostic notation); RFC 8610 (CDDL); AsyncAPI 3.0; Kaitai Struct; Wireshark field model; Khronos glTF Validator; ASAM OpenSCENARIO XML 1.4.0; FMI validation tools.

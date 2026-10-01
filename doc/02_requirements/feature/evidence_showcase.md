<!-- codex-research -->
# Feature Requirements: Evidence Showcase

## Status

Selected by the user on 2026-07-30.

Selected bundle:
`F1-B, F2-B, F3-B, F4-B, F5-A, F6-B, F7-B, F8-B`.

## Goal

Provide one honest, navigable root evidence showcase and shared SSpec/SPipe
evidence contracts that let users verify Simple's critical OS, server, LLM,
GPU, WM, and IDE capabilities from generated manuals without opening test
source.

## Requirements

### REQ-EVS-001 — Root showcase and discoverability

The repository shall provide `EVIDENCE_SHOWCASE.md` at the project root.
`FILE.md` shall allow and describe it, and `README.md` shall link it from a
prominent feature/status or documentation entry point.

### REQ-EVS-002 — Subproject aggregation

The root showcase shall link important subproject `EVIDENCE_SHOWCASE.md` files
when they exist and shall link the authoritative generated SSpec manual for
each critical feature. It shall aggregate links and status rather than copy
feature artifacts.

### REQ-EVS-003 — Evidence status vocabulary

Every critical showcase row shall use exactly one status:
`live-pass`, `historical-pass`, `contract-only`, `blocked`, `unsupported`, or
`planned`. Only a current, provenance-bound receipt may produce `live-pass`.

### REQ-EVS-004 — Receipt-generated truth

Status, provenance, freshness, and artifact links shall be generated from a
versioned evidence receipt/manifest. Human-authored Markdown may provide
categories, explanations, and claim boundaries but shall not override receipt
truth.

### REQ-EVS-005 — Existing evidence owners

The implementation shall extend and reuse
`ScenarioEvidenceArtifact`, `scenario_helpers`, `EvidenceReceipt`, the
canonical SSpec runner/docgen, SGTTI/Draw IR evidence, QEMU/Electron capture,
and screenshot comparison. It shall not introduce a parallel capture,
integrity, hashing, or reporting stack.

### REQ-EVS-006 — Ordered normalized text evidence

One shared text verifier shall:

- strip ANSI and normalize CRLF;
- preserve line boundaries;
- support trim-only or collapsed horizontal whitespace;
- apply only explicitly declared typed masks such as date, version, address,
  duration, and build ID;
- require selected lines in order with optional bounded gaps;
- retain raw and normalized transcripts; and
- report the first missing or out-of-order expected line.

### REQ-EVS-007 — Linux and SimpleOS transcript exemplars

At least one Linux boot/login and one SimpleOS boot/login or shell scenario
shall use the shared text verifier. A source-only marker scan, unordered grep,
or globally space-stripped transcript shall not satisfy this requirement.

### REQ-EVS-008 — Still evidence

Still evidence shall pair structured assertions with a typed artifact recording
format/MIME, dimensions, checksum, producer/version, source revision, host and
target identity, capture readiness, baseline identity, and comparison result.
PNG or lossless WebP shall remain the canonical pixel baseline; SVG is allowed
for vector-native producers; AVIF is presentation-only unless decoded to the
canonical pixel oracle.

### REQ-EVS-009 — Motion and event evidence

Motion evidence shall verify an ordered event receipt and selected keyframes.
Animated WebP and/or WebM may be attached for human review, but encoded video
bytes shall not be the pass/fail oracle. The manifest shall record duration,
event count, keyframe count, checksum, producer, and transcript.

### REQ-EVS-010 — Safe HTML evidence

HTML evidence shall expose HTTP status/headers where applicable, escaped source,
visible text, selector/attribute assertions, and an optional still. Generated
GitHub-facing Markdown shall not execute captured HTML. Any optional local
preview shall use validated canonical paths and a strict sandbox without
scripts, forms, navigation, plugins, or same-origin privileges.

### REQ-EVS-011 — Typed protocol and crypto evidence

Binary/protocol evidence shall retain exact raw-byte assertions and render typed
rows containing offset/range, bit offset/width, mask, endianness, field name,
actual value, expected value, status, importance, and note. Generated
highlighting shall derive from typed importance/status fields and shall link
back to the relevant raw byte range.

### REQ-EVS-012 — SimpleOS QEMU web/database exemplar

One end-to-end scenario shall reuse the existing SimpleOS boot HTTP service and
`SimpleDbService` to prove:

1. boot and server readiness;
2. opening a dynamic HTML page;
3. inserting data;
4. querying the inserted data; and
5. reopening or refreshing the page and observing the row.

The retained evidence shall include serial, HTTP/API transcript, structured
HTML/DOM assertions, database result, and a still artifact.

### REQ-EVS-013 — SimpleOS QEMU WM exemplar

One current-source QEMU WM scenario shall pair QMP/serial or UI-access event
receipts with baseline and post-action keyframes. It shall prove at least one
real focus, input, move, maximize/restore, open/close, or equivalent event
through the canonical production WM route.

### REQ-EVS-014 — IDE exemplar

One production IDE scenario shall prove startup, editing, a command/action,
diagnostic or run output, and interaction delivery. It shall pair semantic
SGTTI/UI-access/Draw IR evidence with a still and short motion artifact, and
shall prove the production entrypoint has no SGTTI/test-only import path.

### REQ-EVS-015 — Local LLM Caret exemplar

One scenario shall prove Caret communicates with a real local Simple-compatible
LLM server: server and model identity, local endpoint readiness, a `hello`
prompt, streamed or complete response, and a retained transcript. A dummy
provider or mocked response may test Caret behavior but shall not satisfy local
model execution.

### REQ-EVS-016 — GPU evidence rung matrix

GPU showcase rows shall report emission, compile/validation, submission,
completion/fence, device-origin readback, and CPU-oracle parity separately.
The showcase shall stop at and display the first unavailable rung rather than
promote source inspection, CPU fallback, or synthetic handles to GPU PASS.

### REQ-EVS-017 — Physical ARM board truth boundary

The ARM-board Clang hello-world row shall require board identity,
flash/download/boot path, Clang compile/link, SimpleOS filesystem placement,
in-guest execution output, exit status, and UART/SSH transcript. QEMU,
host-side compile, or source presence shall be labeled separately and shall not
satisfy the physical-board row.

### REQ-EVS-018 — Generated manual rendering

SPipe docgen shall consume evidence manifests and render:

- safe artifact links;
- embedded TUI text;
- supported still images with alt/summary text;
- motion transcript, keyframes, and compatible review media/fallback links;
- inert HTML source and structured checks; and
- protocol/crypto field tables with text-equivalent highlighting.

Missing required artifacts or invalid paths shall fail closed.

### REQ-EVS-019 — Modern SSpec only

Every new or updated executable scenario shall use `use std.spec.*`,
`describe`, `it`, `step`, `expect`, and built-in matchers. It shall contain
direct value assertions and no legacy Given/When/Then helper flow,
boolean-wrapper assertion, placeholder pass, silent missing-evidence branch, or
executable `.spl` file under `doc/06_spec`.

### REQ-EVS-020 — Spec-to-SSpec later integration

The evidence manifest/oracle contract shall be documented for later integration
with the existing Markdown-to-SSpec generator. Generated regions shall preserve
manual tests, emit modern SSpec for supported oracles, use `pending(...)` for
unsupported examples, and fail closed on malformed/duplicate regions.
Repository-wide migration is not part of the first implementation.

### REQ-EVS-021 — Workflow guidance consistency

Any implementation changing SPipe/SSpec evidence behavior shall update the
matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`, `.agents/skills/`,
`.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/` guidance.
Generated manuals shall be reviewed as operator manuals without opening the
source spec.

## Selected exemplar scope

The first implementation shall design one exemplar for each evidence class:

| Evidence class | Exemplar |
|---|---|
| Text | Linux plus SimpleOS boot/login |
| HTML/API/DB | SimpleOS dynamic page insert/query |
| UI motion | SimpleOS QEMU WM |
| IDE | Production IDE edit/action/diagnostic |
| Protocol/crypto | Typed bitfield table |
| LLM | Real local Caret `hello` |
| GPU | Evidence-rung matrix with live or explicit blocker status |

Unavailable host/hardware rows remain visible with exact prerequisites and
resume commands; they do not block publication of a truthful showcase.

## Out of scope for the first implementation

- A new standalone evidence database or interactive packet-inspector app.
- Byte-exact encoded video comparison.
- Raw executable HTML in generated Markdown.
- Repository-wide spec-to-SSpec migration.
- Promoting historical, source-only, QEMU-only, mocked, fallback, or blocked
  evidence to a broader live claim.

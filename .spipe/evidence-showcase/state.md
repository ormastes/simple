# Feature: Evidence Showcase

## Raw Request

Create `EVIDENCE_SHOWCASE.md` for the main Simple project and link important
subproject showcases. Cover working evidence for Simple RISC-V boot/login,
SimpleOS boot, Clang-compiled hello world executed from the SimpleOS
filesystem on an ARM board, SimpleOS web and database servers with dynamic
page open/query/insert flows, local LLM server/client caret hello flow, GPU
programming, SimpleOS QEMU window manager, and the IDE.

Use SSpec/SPipe to generate user-checkable text or captured image evidence.
Prefer TUI capture for UI cases; still captures may use SVG/AVIF, while event
handling and motion may use animated WebP/WebM. Large binary evidence may use
Git LFS. Improve still/motion verification, whitespace-tolerant and
volatile-field-tolerant text verification for Linux and SimpleOS boot/login,
HTML evidence embedding in generated manuals, and bitfield/table protocol and
crypto evidence with important-field highlighting. Reduce duplicated
verification logic, make generated evidence easy for users to inspect, update
SPipe guidance, and plan the later spec-to-SSpec migration.

## Task Type

feature

## Refined Goal

Provide one honest, navigable evidence index and shared SSpec/SPipe evidence
contracts that let users verify Simple's critical OS, server, LLM, GPU, WM, and
IDE capabilities from generated manuals without opening test source.

## Acceptance Criteria

- AC-1: Repository research inventories existing showcase/index files, SSpec
  evidence helpers, generated manuals, capture formats, storage policies, and
  representative feature evidence without modifying unrelated active lanes.
- AC-2: Domain research compares established text normalization, visual
  regression, motion capture, HTML-report embedding, binary/protocol
  visualization, and artifact-retention practices using primary sources.
- AC-3: Feature and NFR option documents provide 2-4 selectable choices with
  description, pros, cons, effort, and explicit user-selection status.
- AC-4: The selected design defines a root `EVIDENCE_SHOWCASE.md` and a
  discoverable convention for linking important subproject
  `EVIDENCE_SHOWCASE.md` files and recent generated feature manuals.
- AC-5: Every showcase claim records status and provenance and distinguishes
  live PASS evidence from source-only, cached, blocked, unsupported, or planned
  evidence; unavailable hardware is never promoted to PASS.
- AC-6: The coverage plan includes RISC-V boot/login and Linux boot/login text
  evidence with line-oriented matching that can normalize whitespace and
  explicitly mask dates, versions, addresses, and other declared volatile
  fields while still failing on missing or reordered required content.
- AC-7: The coverage plan includes SimpleOS boot/login, the QEMU window
  manager, and event-delivery evidence, with still and motion artifacts where
  those artifacts prove materially different behavior.
- AC-8: The coverage plan includes physical ARM board identity, boot/download
  path, Clang compilation of hello world, filesystem placement, and in-guest
  execution; QEMU-only or source-present results cannot satisfy the board row.
- AC-9: The coverage plan includes SimpleOS web-server and database-server
  evidence for opening a dynamic page and observing query and insert behavior,
  including structured HTML/DOM or response assertions before screenshots.
- AC-10: The coverage plan includes local Simple LLM infrastructure and a
  client/caret hello interaction with model/server identity and transcript
  provenance, without treating a mocked response as local-model execution.
- AC-11: The coverage plan includes GPU programming evidence with emitted
  program, compile, submission, completion, device-origin readback, and
  CPU-oracle status kept as separate evidence rungs.
- AC-12: The coverage plan includes IDE startup, editing, command/action,
  diagnostic or run result, and user interaction evidence, reusing canonical UI
  test and capture routes and proving the production entrypoint has no test-only
  dependency.
- AC-13: Still-image evidence has a structured manifest with format, dimensions,
  checksum, producer, capture time, comparison mode, baseline identity, and
  readable generated-manual rendering; SVG/AVIF support is selected based on
  actual producer and review needs.
- AC-14: Motion evidence has a structured manifest with format, duration/frame
  or event count, producer, event transcript, checksum, and readable
  generated-manual rendering; animated WebP/WebM support is selected based on
  browser/manual compatibility and verification needs.
- AC-15: HTML evidence is sanitized and embedded or linked in generated SSpec
  manuals so a user can inspect both rendered output and structured assertions
  without executing untrusted active content.
- AC-16: Crypto and protocol evidence can render bitfield/table views with byte
  offsets, widths, decoded values, expected values, and important-field
  highlighting while retaining exact machine-checkable byte assertions.
- AC-17: Shared evidence helpers replace repeated per-spec normalization,
  capture metadata, artifact-link, and protocol-table logic; the plan identifies
  concrete duplication to remove and does not add parallel helper stacks.
- AC-18: The spec-to-SSpec direction is documented as a later migration with
  prerequisite spec-format gaps and fail-closed generation rules; it is not
  presented as completed by this planning lane.
- AC-19: Architecture, detail design, system-test plan, representative SSpec
  scenario design, generated-manual layout, and agent-task ownership are
  traceable to these acceptance criteria after the user selects requirements.
- AC-20: Final verification for any later implementation checks matching
  `doc/07_guide`, `doc/06_spec`, `.codex/skills/`, `.agents/skills/`,
  `.claude/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/` guidance;
  generated manuals must work as operator-facing evidence pages.
- AC-21: Every new or updated executable scenario uses the modern SSpec surface
  (`use std.spec.*`, canonical `describe`/`it`/`step`/`expect`, and built-in
  matchers), contains direct value assertions, and contains no legacy
  `Given_*`/`When_*`/`Then_*` flow, boolean-wrapper assertion, placeholder
  pass, or executable `.spl` file under `doc/06_spec`.

## Scope Exclusions

- This research/planning lane does not claim currently unavailable hardware or
  renderer rows as passing.
- Executable specs, evidence-manifest/docgen implementation, and release are
  outside this completed research/design lane.
- The root showcase aggregates authoritative evidence; it does not copy every
  artifact or replace feature manuals.

## Cooperative Review

- Research sidecars: existing SSpec/SPipe infrastructure; OS/board/WM evidence;
  web/database/HTML evidence; UI/IDE/still/motion evidence; LLM/GPU/protocol
  evidence; domain standards and artifact formats.
- Merge owner and final normal/highest-capability reviewer: root Codex agent.
- Selected shared interfaces preserve `ScenarioEvidenceArtifact` and
  `EvidenceReceipt`, then add `ScenarioEvidenceManifest`,
  `ScenarioTextEvidencePolicy`, `ScenarioMotionEvidence`, and
  `ScenarioProtocolFieldEvidence` in their documented runtime-family owners.
- Manual `step("...")` flow names: `Capture the feature evidence`,
  `Verify the structured evidence`, `Render the evidence for review`, and
  `Publish the showcase link`.
- Tentative setup/checker helpers:
  `prepare_evidence_workspace`, `check_text_evidence`,
  `check_visual_evidence`, `check_html_evidence`, and
  `check_protocol_evidence`; reuse or rename existing canonical helpers when
  found.
- Any temporary generated/helper path must fail explicitly with
  `assert(false)` or `fail(...)`; placeholder PASS is forbidden.
- Generated-manual review owner: root Codex agent after independent sidecar
  inventory, with user selection required before design acceptance.

## Phase

design-complete

## Log

- dev: Created state file with 21 acceptance criteria (type: feature).
- dev: Added SimpleOS QEMU WM and IDE evidence from the user addendum.
- dev: Added modern-SSpec-only requirement for all new or updated scenarios.
- research: Added local/domain research and feature/NFR option documents.
- research: Paused before final requirements and design for mandatory user
  selection.
- requirements: User selected the recommended feature bundle
  `F1-B, F2-B, F3-B, F4-B, F5-A, F6-B, F7-B, F8-B` and all recommended NFRs
  `N1-B` through `N10-B`; wrote final requirements and removed option files.
- design: Added architecture, TLDR, TUI/GUI/detail design, system-test plan, and
  agent-task plan after six parallel read-only reviews.
- showcase: Added the root and OS/IDE/LLM/GPU evidence hubs with qualified
  statuses and repository navigation. Receipt-backed status generation remains
  implementation work.

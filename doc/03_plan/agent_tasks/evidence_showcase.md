<!-- codex-design -->
# Agent Task Plan: Evidence Showcase

## Scope

Dependency-ordered implementation plan for the selected requirements. Parallel
lanes may begin only after Lane 0 freezes the shared contract.

## Frozen shared contract

### Types

- `ScenarioEvidenceManifest`
- `ScenarioEvidenceArtifact` (preserved, additive fields only)
- `EvidenceReceipt` (preserved)
- `ScenarioTextEvidencePolicy`
- `ScenarioTextMask`
- `ScenarioTextMatchResult`
- `ScenarioMotionEvidence`
- `ScenarioProtocolFieldEvidence`

### Manual steps

- `Capture the feature evidence`
- `Verify the structured evidence`
- `Render the evidence for review`
- `Publish the showcase link`

### Setup/checkers

- `prepare_evidence_workspace`
- `check_text_evidence`
- `check_visual_evidence`
- `check_html_evidence`
- `check_protocol_evidence`

### Fail-fast rule

Any temporary helper must call `fail("not implemented: <name>")` or
`assert(false)`. Silent no-op, default success, missing-evidence success, and
placeholder assertions are forbidden.

## Ownership

- Merge owner: primary Codex implementation session.
- Final reviewer: separate normal/highest-capability review session; must differ
  from merge owner for done marks and generated-manual quality.
- Lower-model sidecars: allowed for bounded mechanical specs/docs after Lane 0;
  their output requires merge-owner review.
- User-authorized parallel work: yes, 2026-07-30.

## Lanes

### Lane 0 — Contract and ownership freeze

**Owner:** merge owner
**Depends on:** selected requirements/design
**Files:** common evidence type exports, manifest schema contract, lane state
**Deliverables:**

- exact schema/version/status/path conventions;
- compile-visible type/constructor signatures;
- per-lane file ownership with no overlap;
- fail-first fixtures for unsupported major, missing artifact, and blocker;
- no implementation registry/database.

**Gate:** high-capability review accepts schema and layering.

### Lane 1 — Text evidence vertical slice

**Sidecar suitability:** bounded Simple implementation/spec work
**Depends on:** Lane 0
**Owns:**

- `scenario_text_evidence.spl`;
- its unit/system fixtures;
- Linux RISC-V and SimpleOS serial integrations.

**Deliverables:**

- ordered normalization/masks/mismatch diagnostics;
- raw/normalized artifacts;
- hardened Linux/SimpleOS producer contracts;
- modern SSpec/manuals.

**No-false-green:** reordered lines, invalid masks, echoed input, and nonzero/
unbounded QEMU exits fail.

### Lane 2 — Artifact integrity, still, and motion

**Sidecar suitability:** bounded manifest/media validation
**Depends on:** Lane 0
**Owns:**

- additive artifact integrity fields;
- `scenario_motion_evidence.spl`;
- path/MIME/size/checksum validation helpers;
- WM/IDE media manifest adapters;
- LFS policy only when first retained format exists.

**Deliverables:** semantic event + keyframe oracle and bounded review media.

**No-false-green:** encoded WebM/WebP never decides PASS.

### Lane 3 — HTML and protocol rendering

**Sidecar suitability:** separate HTML and protocol fixture subtasks
**Depends on:** Lane 0
**Owns:**

- `scenario_protocol_evidence.spl`;
- inert HTML render model;
- typed protocol table/raw-byte anchors;
- Markdown fence/alt/link/table escaping;
- docgen negative fixtures.

**Deliverables:** safe generated manual fragments and protocol exemplar.

**No-false-green:** raw HTML never executes; typed mismatch cannot be hidden by
highlighting.

### Lane 4 — Runner, manifest, docgen, showcase

**Owner:** merge owner or strongest implementation agent
**Depends on:** Lane 0; consumes stable outputs from Lanes 1-3
**Owns:**

- `scenario_evidence_manifest.spl`;
- `EvidenceReceipt` adapter;
- pure-Simple runner persistence;
- `spipe_docgen/evidence_manifest.spl`;
- focused manifest lookup;
- `config/evidence_showcase.sdn`;
- root/subproject generated-region logic;
- `EVIDENCE_SHOWCASE.md`, `FILE.md`, `README.md`, `config/FILE.md`.

**Deliverables:** atomic fail-closed manifest and receipt-derived showcases.

**No-false-green:** status cannot be hand-overridden; missing manifest/artifact
cannot disappear.

### Lane 5A — SimpleOS web/database

**Depends on:** Lanes 1, 3, 4
**Owns:** existing `http_baremetal`/`SimpleDbService` route, QEMU producer, DB
dynamic page spec/manual.
**Deliverable:** boot → page → insert → query → refreshed page evidence.
**Constraint:** reuse existing server; do not add another web/DB service.

### Lane 5B — WM and IDE

**Depends on:** Lanes 2, 4
**Owns:** existing WM fullscreen evidence and production IDE launch/interaction
path plus their specs/manuals.
**Constraint:** Office/feature-check evidence cannot substitute for the IDE;
historical WM PASS cannot override current failure.

### Lane 5C — LLM, GPU, RISC-V/ARM

**Depends on:** Lanes 1, 2, 4
**Owns:** Caret local-model spec, GPU receipt aggregate, physical ARM blocker/live
contract, and related manuals.
**Constraint:** dummy/local readiness/fallback/source inspection cannot become
live model/GPU/board evidence.

### Lane 6 — Workflow documentation and templates

**Sidecar suitability:** mechanical cross-surface updates after names freeze
**Depends on:** CLI/schema/annotations final from Lane 4
**Owns:**

- canonical guides and generated examples;
- Codex/agent/Claude/Gemini SPipe workflow surfaces;
- stale `use std.spec` and Given/When/Then templates;
- IDE/simple-ui evidence guidance.

**Deliverable:** every touched process surface teaches the same modern
SSpec/manifest/showcase contract.

**Upstream boundary:** `.spipe/spipe` is a separate repository/gitlink. Generic
upstream SPipe changes use a separate commit/lane and parent gitlink update; do
not fold them invisibly into host-only docs.

### Lane 7 — Final review and verification

**Owner:** independent highest-capability reviewer
**Depends on:** all selected implementation lanes
**Checks:**

- requirement/NFR traceability;
- generated-manual quality and accessibility;
- stale/current claim precedence;
- traversal/symlink/MIME/Markdown/HTML security;
- modern SSpec and no placeholders;
- no production evidence imports/hot-path scans;
- performance/size limits;
- workflow mirror consistency;
- root/subproject showcase truth; and
- explicit unresolved blocker/resume rows.

## Dependency graph

```text
Lane 0
  ├─ Lane 1 text
  ├─ Lane 2 media
  └─ Lane 3 html/protocol
        \   |   /
          Lane 4 runner/docgen/showcase
             ├─ Lane 5A web/db
             ├─ Lane 5B wm/ide
             └─ Lane 5C llm/gpu/arm
                       |
                    Lane 6 docs
                       |
                    Lane 7 review
```

Lane 4 may implement consumers against frozen Lane 0 fixtures while Lanes 1-3
run, but it must not merge incompatible private schemas.

## Planned workflow update matrix

### Required host repository updates

- root `AGENTS.md`, `FILE.md`, `README.md`
- `config/FILE.md`
- `doc/07_guide/{README.md,infra/sspec_scenario_manual.md,infra/testing.md}`
- `doc/07_guide/app/spipe/evidence_showcase.md`
- `doc/07_guide/app/spipe/scenario_manual_example.md`
- relevant GUI/web and baremetal/protocol manual examples
- `test/README.md`, `doc/06_spec/FILE.md`, `src/app/README.md`
- `.codex/skills/{sp_dev,design,system_test,impl,verify,release}/SKILL.md`
- `.agents/skills/{design,impl,verify,release}/SKILL.md`
- `.claude/skills/{spipe,design,impl,verify,release}.md`
- `.claude/skills/lib/{spipe_phases,test,doc}.md`
- `.claude/rules/testing.md`
- `.claude/agents/docs.md`
- `.claude/agents/spipe/{dev,arch,spec,implement,refactor,verify,ship}.md`
- `.claude/templates/spipe_template.spl`
- `.gemini/commands/{sp_dev,design,impl,verify,release,visual_test}.toml`
- `.codex/skills/{simple-ui,ide-office}/SKILL.md` when their exemplars land

### N/A unless their surface changes

- research skill/agent
- general coding skill
- lightweight command pointers that only redirect to canonical SPipe guidance

## Later spec-to-SSpec lane

After schema stabilization:

- update only the existing `migrate_spec_to_spl.spl`;
- preserve bytes outside generated markers;
- reject malformed/duplicate markers before write;
- emit modern direct assertions only for supported oracles;
- emit `pending(...)` otherwise;
- keep capture backends, receipt I/O, docgen, and showcase curation out of the
  generator.

This future lane is not a dependency for the first showcase implementation.

## Completion checklist

- [ ] Lane 0 contract reviewed.
- [ ] Lanes 1-3 pass focused fixtures.
- [ ] Lane 4 produces atomic validated manifests and root/subproject pages.
- [ ] Selected exemplars have live receipts or honest blocker rows.
- [ ] All workflow mirrors are current.
- [ ] Generated manuals are operator-readable and zero-stub.
- [ ] Traceability is 100%.
- [ ] Final independent review reports PASS or lists unresolved blockers.

# Simple RenderDoc Feature Expert

## Role

Own SPipe/LLM process knowledge for **Simple RenderDoc**, the repo-native
**Simple 2D RenderDoc Backend Equivalence** capsule. It is Simple's counterpart
for deterministic render records, validation, field-level diff, exact
equivalence, guest/board receipts, and external capture inspection. It is not a
RenderDoc fork and is broader than the `capture-simple` wrapper.

## Implemented Core

```sh
bin/simple test test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl --mode=interpreter
bin/simple test test/02_integration/rendering/backend_render_equivalence_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/renderdoc_replay_inspect_spec.spl --mode=interpreter
```

These cover the pure record model, fail-closed validation, canonical form,
first/all differences, exact equivalence policy, and pure-Simple parsing of
RenderDoc XML conversion. Focused verification passed 6/6, 5/5, and 5/5 on
2026-07-27.

## External Capture Bridge

```sh
scripts/tool/renderdoc-evidence.shs capture-simple
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
```

External `.rdc` replay-open/action evidence corroborates the Simple record; it
does not replace the record, exact pixel oracle, or independent producer. The
producer emits a lowercase SHA-256 and the Simple gate recomputes it before and
after replay so substituted or concurrently changed capture bytes fail closed.

## Current Gaps

- Fresh native Windows/macOS, physical-board, and live RenderDoc evidence
  remains external to a Linux-only run.
- A host-matched deployed pure-Simple release binary is mandatory; a Rust seed
  is rejected rather than accepted as capture or SSpec evidence.
- QEMU and full bootstrap qualification must run in a fresh environment after
  their bounded retry caps are exhausted.

Until these are implemented, report the counterpart as **core implemented,
aggregate incomplete**.

## Aggregate

```sh
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --self-test
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=focused
```

The wrapper reports all focused, QEMU, and external rows, rejects non-Stage-4
Simple binaries, preserves leaf logs/artifacts, measures elapsed time and RSS,
and exposes every explicit fail helper as a blocker. Its SSpec contract is
`test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl`.
The 2026-07-27 focused lane remains blocked where a deployed pure-Simple runner
or live RenderDoc/native-host artifact is unavailable.

## Owners

- Requirements: `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- Architecture: `doc/04_architecture/simple_2d_renderdoc_backend_equivalence.md`
- Design: `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- Core: `src/lib/common/renderdoc/backend_render_record.spl`
- RDC inspector: `src/app/test/renderdoc_replay_inspect.spl`
- QEMU/board schemas: `src/lib/common/renderdoc/simpleos_render_target_evidence.spl`,
  `src/lib/common/renderdoc/simpleos_simd_render_evidence.spl`
- Guide: `doc/07_guide/tooling/renderdoc_capture_infra.md`
- Shared tool: `scripts/tool/renderdoc-evidence.shs`
- Shared capture/schema helper: `scripts/lib/renderdoc-evidence-common.shs`
- Glossary: `doc/glossary.md`

## Update Rule

When record schema, facade capture, QEMU receipts, external bridges, or
acceptance rules change, update this entry and the canonical guide in the same
SPipe lane. Never replace explicit fail placeholders with false-green passes.

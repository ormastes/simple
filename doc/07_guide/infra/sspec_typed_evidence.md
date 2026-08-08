# Modern SSpec Typed Evidence

**Status:** Wave-0 contract landed 2026-08-08, and Wave-1/Wave-2 lanes E2, E2b,
E3, E4, E6, E7a, E7b landed the same day — the shared contract, every format
adapter, action-trace, manual rendering, and the spec-to-spipe extension
namespace all exist and are unit-covered. What has **not** landed: the
`spipe_docgen` evidence loader/wiring (E5), the `sspec-maintain evidence`
commands, any live capture provider, and the three reference example manuals
(E8) — see §8. See §9a for four open red-team findings that gate treating the
comparator as fully trustworthy.
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
| Executable behaviour of all of the above | `test/01_unit/lib/common/spec/evidence/*_spec.spl` — 8 spec files, 1,862 lines, 124 `it` examples total |
| `spipe_docgen` evidence loader + renderer wiring, live capture providers, `sspec-maintain evidence` commands, reference examples | not yet implemented — §8 |

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
use std.common.spec.evidence.model.{
    check_exact, check_full_pattern, check_ignore, check_multiset,
    check_bind, check_same_as, oracle_spec
}
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
| Closed-mode undeclared field fails | New fields enter the contract without anyone deciding |
| Zero positive resolutions fails | A pattern-only oracle reports a clean pass over an empty observation |

Expected values may never be derived from the actual observation under test — that is
equality with itself, not verification.

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

## 8. Not yet implemented

These are design-only today. Do not cite them as working behaviour; lanes are tracked in
`doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`.

| Capability | Lane |
|---|---|
| TUI terminal-cell capture and scoped cell diff | E2 |
| GUI action trace, bounded settling, `wm_compare` adapter | E2 |
| Text protocol grammar adapters and frame envelope | E3 |
| Binary layout IR and production accessor binding | E4 |
| `spipe_docgen` evidence loader and block renderer | E5 |
| `spec-to-spipe` evidence extension namespace | E6 |
| 2D / 3D / simulation / audio / ML profiles | E7 |
| The three runnable reference example manuals | E8 |

Until E5 lands, `comparison_to_manual_blocks` produces blocks that no generator consumes
yet; it is contract-complete and unit-covered, not wired end to end.

## 9. Running the coverage

```bash
bin/simple run test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl
```

Use `run` rather than `test` for this spec: the `test` daemon path exceeds its
800-module transitive-import cap while loading, which surfaces as a load error rather
than a spec result. Verified 2026-08-08: 24 examples, 0 failures, exit 0; with the
vacuity gate and the pattern length check deliberately sabotaged, 2 examples go red and
the run exits 1.

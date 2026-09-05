# sspec-maintain: Typed-Evidence Findings and Commands — Design

**Status:** Design only. This document specifies an extension to
`src/app/sspec_maintain/**`; no source under that path is touched by this
document. A later lane implements it.

**Inputs:** `doc/07_guide/infra/sspec_documentization_maintenance.md` (operator
manual), `src/app/sspec_maintain/{rules,score,model,main}.spl` (verified
source), `doc/07_guide/infra/sspec_typed_evidence.md` (Wave-0 evidence
contract), `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`
§9 (the finding table and command list this document expands).

---

## 1. Existing surface, verified

### 1.1 Finding catalog

`sspec_rule_definitions()` in `src/app/sspec_maintain/rules.spl:4-29` returns a
flat `[SspecRuleDefinition]` — one array literal, 24 entries as of this audit,
each an inline constructor with no dynamic registration. There is no plugin
registry, no per-repo config layer, and no separate "evidence rules" module —
every rule id, dimension, severity, deduction, blocker flag, detection prose,
rationale, false-positive-limit prose, suppression policy, and safe-edit flag
lives in this one array. `sspec_rule_definition(rule_id)` (`rules.spl:31-35`)
does a linear scan for lookup by id. `sspec_lint_rule_references()`
(`rules.spl:37-39`) is a separate, non-`SspecRuleDefinition` list of
`SPIPE001..007` strings — those remain lint-owned and are referenced, not
reimplemented, matching the guide (`sspec_documentization_maintenance.md:88-90`).

The `SspecRuleDefinition` shape (inferred from every call site in
`rules.spl`, confirmed against `model.spl`) carries: `rule_id: text`,
`dimension: text`, `default_severity: text`, `deduction: i64`, `blocker: bool`,
`title: text`, `detection: text`, `rationale: text`,
`false_positive_limits: text`, `suppression_policy: text`, `safe_edit: bool`.
This is a *definition* record — static metadata. The actual per-instance hit
is `SspecDocumentizationFinding` (`model.spl:72-87`):
`rule_id, dimension, severity, confidence, path, line, column, end_line,
end_column, evidence, rationale, remediation, fingerprint, baseline_state,
score_deduction`. Detection logic that produces these findings lives outside
`rules.spl` — in `src/app/sspec_maintain/analyzer.spl` and
`source_facts.spl` — `rules.spl` only declares the catalog metadata each
producer must match against.

**Dimensions actually in use** (from the 24 definitions): `narrative`,
`structure`, `oracle`, `traceability`, `evidence`, `coverage`,
`maintainability`. These are exactly the seven scored dimensions.

### 1.2 Scoring and the "any blocker clamps to 49" behaviour

`score_sspec_findings()` in `src/app/sspec_maintain/score.spl:9-42` is
verified as follows. Each dimension starts at 100 (`score.spl:10-16`). For
every finding, `score_deduction` is subtracted from its `dimension`'s running
total (`score.spl:19-26`), and a `blockers` counter increments once per
finding with `finding.blocker == true` (`score.spl:26`) — note this counts
*findings* flagged blocker, not distinct blocker *rules*; two blocker hits
from the same rule count as two. Each of the seven dimension totals is then
clamped to `[0, 100]` by `_score_clamp` (`score.spl:4-7`, applied at
`score.spl:27-33`). The weighted `raw` aggregate is computed at
`score.spl:34-35`:

```
raw = (narrative*15 + structure*15 + oracle*20 + traceability*15
     + evidence*15 + coverage*10 + maintainability*10) / 100
```

— weights sum to 100, matching the guide's table
(`sspec_documentization_maintenance.md:73-81`). The clamp line,
`score.spl:36`:

```simple
val effective = if blockers > 0 and raw > 49: 49 else: raw
```

confirms the documented behaviour exactly: **any** finding with
`blocker: true` (currently only `SSDOC-ORA-001`, `SSDOC-ORA-002`,
`SSDOC-TRC-002`, `SSDOC-TRC-003` per the catalog) caps `effective_aggregate`
at 49 regardless of how high `raw` is, and `release_ready` is
`blockers == 0` (`score.spl:42`) — independent of the numeric score entirely.
Both `raw_aggregate` and `effective_aggregate` are retained on
`SspecDocumentizationScore`, matching the operator guidance to rank by `raw=`
(`sspec_documentization_maintenance.md:56-60`, `.claude/rules/testing.md`
"Modernization signals"). **No contradiction found**: the research doc and
memory notes describe this accurately; this document treats it as ground
truth for the new findings below (§2) and commands (§3).

### 1.3 Where research §9 is imprecise

Research §9's tool-plan table (`modern_sspec_typed_evidence_research_2026-08-08.md:589-623`)
lists commands as if they already exist ("Reuse: `simple sspec-maintain
scan|documentize <spec>`"). Verified against `main.spl:512-526`
(`run_sspec_maintain`): the dispatch is a flat `if` chain over `operation` —
`scan`, `improve`, `scaffold`, `documentize` only. There is **no** `evidence`,
`verify-examples`, or `--profile-completeness` branch anywhere in
`src/app/sspec_maintain/`, and `simple test` (a different binary entry point
entirely, not in this directory) has no `--update-evidence`/
`--accept-evidence` flags. This is not a contradiction of substance — research
§8 already says the evidence pipeline itself is "design-only" — but §9's table
reads as a reuse list when three of its four reused items are aspirational.
This document treats all four new commands (§3) and all sixteen new rule ids
(§2) as wholly new work, not "extend an existing branch."

A second imprecision: research §9 implies findings are looked up/rendered
generically. In the real code, `_run_scan` (`main.spl:154-296`, not fully
read here but referenced by the guide's diagnostics description) filters,
baselines, and renders `SspecDocumentizationFinding` values that some
producer already built from `sspec_rule_definitions()`. Any new finding code
needs both (a) a catalog entry in `rules.spl` and (b) a producer that walks
parsed spec/evidence-declaration source and emits matching
`SspecDocumentizationFinding` values — the catalog alone documents a rule ID,
it does not detect anything. §5 makes this split explicit per rule.

---

## 2. New finding codes

Source for definitions: research §9 table
(`modern_sspec_typed_evidence_research_2026-08-08.md:603-621`) and the
fail-closed rule table in the typed-evidence guide
(`doc/07_guide/infra/sspec_typed_evidence.md:116-129`). Each entry below adds
the fields a `SspecRuleDefinition` requires (§1.1 shape) plus a false-positive
analysis, since the existing catalog treats "false_positive_limits" as
load-bearing prose reviewers rely on, not decoration.

All fifteen new rules join the existing `evidence` dimension except
`SSDOC-UI-*`, `SSDOC-TUI-101`, `SSDOC-PROTO-*`, `SSDOC-BIN-*`, and
`SSDOC-MAN-101`, which are new sub-areas within `evidence` and
`maintainability` respectively — see the Dimension column. None of these
rules can run against source that has no `EvidenceRequest`/`OracleSpec`
declarations at all: with zero evidence declared, all sixteen rules are
vacuously silent, which is correct — a spec choosing not to use typed
evidence yet is not itself an evidence-quality defect (that gap is what
`SSDOC-EVD-001`, already in the catalog, covers).

| Rule | Dimension | Severity | Blocker | Deduction (proposed) | Detection rule | False positives it must avoid |
|---|---|---|---|---:|---|---|
| `SSDOC-EVD-101` | evidence | warning | no | 15 | A capture site (`capture_*`/`expect_evidence`/`expect_protocol`/`expect_binary` call, or a `ScenarioEvidence`-style free-form record) exists in a scenario whose `profile_id` matches a registered `EvidenceProviderRegistry`/`FormatAdapterRegistry` profile, but the capture uses the legacy free-form `ScenarioEvidence` API instead of `oracle_spec(...)`. | A spec predating typed evidence for a profile with no registered adapter yet (most of the repo, per guide §8) must not trip this — the rule only fires when a matching typed profile is *registered*, not merely conceivable. Requires an explicit profile→adapter registry snapshot as input, not string-matching a capture kind name. |
| `SSDOC-EVD-102` | evidence | blocker | yes | 40 | An `OracleSpec` check's selector resolves to zero nodes, or to more than one node while the check declares single cardinality, against the `CanonicalEvidence` produced for the same run. | This is a *runtime* fact (selector resolution against captured data), not a static source pattern — it can only be detected by re-running `compare_evidence` and reading `ComparisonResult`, never by grepping `.spl` text. The design must record this as "static scan cannot evaluate this rule"; only `sspec-maintain evidence --explain` (§3.1, which loads real evidence) can, and only for evidence that was actually captured this run. |
| `SSDOC-EVD-103` | evidence | warning | no | 10 | A `check_ignore(path, reason)` call where `reason` is an empty string or matches a placeholder list (`"TODO"`, `"todo"`, `""`). | The comparator itself already fail-closes an empty reason per the guide (`sspec_typed_evidence.md:96,126`) — this is a lint-time *duplicate* signal so a reviewer sees it before running the spec. False positive: a legitimately short but real reason (`"server clock"`, 14 chars) must not be flagged by length alone; gate on exact-empty or the placeholder list only, never a minimum length heuristic. |
| `SSDOC-EVD-104` | evidence | blocker | yes | 50 | A `ComparisonResult` shows a `FullPattern`/pattern-mode check with zero resolved selector matches (mirrors guide rule "Zero positive resolutions fails", `sspec_typed_evidence.md:129`). | Same as EVD-102: a runtime-only fact. Static source scanning cannot distinguish "pattern intentionally matches nothing this run" from "pattern is broken" without executing the comparator. Record as evidence-run-only, not scan-time. |
| `SSDOC-EVD-105` | evidence | blocker | yes | 50 | A generated manual (`doc/06_spec/**` mirror) contains a "Generated from" / source-attribution line naming a `*_spec.spl` path that does not exist on disk, **or** whose file exists but does not contain the evidence-block markers the manual claims to show. | This is the rule that must catch the three 2026-08-08 defects (§4) — file-existence is fully mechanical and zero-false-positive by construction (a path either resolves or not). The second half (claims markers the source lacks) needs a defined marker convention (§4) to avoid flagging a legitimately terse manual; until that convention exists, ship only the file-existence half and record the marker half as not-yet-detectable. |
| `SSDOC-EVD-106` | evidence | warning | no | 20 | The `EvidenceManifest`'s recorded `spec_sha256`/`provider_version`/`artifact_sha256` (per `evidence_manifest_is_complete`, `sspec_typed_evidence.md:159-161`) does not match a freshly recomputed hash of the current spec file / provider binary. | Runtime/manifest-file fact, not source-pattern. Needs the manifest sidecar to exist; if a spec has no manifest yet (pre-typed-evidence), silently skip rather than flag "stale" — staleness presupposes a prior manifest existed. |
| `SSDOC-EVD-107` | evidence | blocker | yes | 50 | A `ComparisonResult` has zero `EvidenceCheckResult` entries whose mode is a positive assertion mode (`Exact`, `FullPattern`, `NumericTolerance`, `Multiset`, `OrderedSequence`, `Invariant`, …) — every check present is `Ignore`-mode. Mirrors "All-ignore oracle fails" (`sspec_typed_evidence.md:127`). | Runtime-only (needs the actual `OracleSpec`/`ComparisonResult`, not source text, since an oracle can be built programmatically). A spec with genuinely zero evidence checks (not using typed evidence at all) must not trip this — gate on "an `OracleSpec` was constructed and evaluated" as precondition, never on "this spec exists." |
| `SSDOC-UI-101` | evidence | warning | no | 15 | An interactive scenario's only evidence assertion is an image/pixel comparison (`gui_image`/`pixel_*`) with no accompanying semantic-state check (`ui.check_text`, `check_visible`, canonical-node assertion, or `tui_grid`/`semantic_ids` in the same `expect_evidence` call). | A scenario whose requirement genuinely *is* pixel-exact rendering (declared via `pixel_exact`/`pixel_masked_exact` with an explicit "visual output is the requirement" marker per guide §3, `sspec_typed_evidence.md:59-61`) must be exempt — detect the exemption via an explicit marker/annotation the scenario authors, not by inferring intent from prose. Without that marker convention this rule risks flagging every deliberate visual-regression spec; ship the marker requirement alongside the rule. |
| `SSDOC-UI-102` | structure | warning | no | 15 | Source contains a fixed-duration wait (`sleep(`, `wait_ms(`, `time.sleep`) between an action call and the following `capture_surface`/`expect_evidence` in the same scenario, with no intervening bounded-settle call (`wait_until`, `settle(`, poll helper). | A `sleep(` used for an unrelated purpose (e.g., rate-limiting a load-test loop, not gating a capture) must not trip this — scope detection strictly to a sleep positioned between an action and the immediately following capture call, not any sleep anywhere in the file. |
| `SSDOC-TUI-101` | evidence | advice | no | 10 | A `tui_grid`/terminal-cell capture/comparison call has no accompanying width-profile declaration (`width_profile`, locale, or explicit East-Asian-width policy per `TerminalWidthProfile`, `sspec_typed_evidence.md` / research §4.3). | A TUI capture using only ASCII fixtures genuinely has no width-ambiguity to declare; this is exactly the kind of rule that "cannot be detected without false positives" per the assignment's instruction — record it as advice-only, never a blocker, and note in the false-positive analysis that source scanning cannot determine whether a given fixture's text is width-ambiguous without executing Unicode segmentation, so this rule is a coarse presence/absence check on the declaration, not a correctness check on its content. |
| `SSDOC-PROTO-101` | evidence | warning | no | 15 | A protocol-parsed comparison (`protocol_oracle`/`compare_protocol`-shaped call) exists with no retained raw-transcript artifact reference (guide: "raw bytes remain retained", research §5.4) in the same evidence declaration. | A synthetic/generated fixture in a *unit* test of the comparator itself (not a system-test protocol capture) legitimately has no "raw transcript" to retain, since there is no real wire capture. Scope this rule to `test/03_system/**` and `test/02_integration/**` protocol specs only; exempt `test/01_unit/**` comparator-internals specs by path. |
| `SSDOC-PROTO-102` | evidence | blocker | yes | 40 | A protocol comparison check uses a value that looks like a regex/wildcard pattern (`.*`, `\d+`, `[0-9]+`) directly as an `exact`/`check_exact` expected value, instead of `check_full_pattern`/`full_pattern`. | A `check_exact` field whose *actual protocol value* legitimately contains regex metacharacters as literal text (e.g. a field that really is the string `".*"`) is indistinguishable from misuse by string inspection alone. Restrict detection to the argument literal appearing inside `check_exact`/`exact(` call syntax specifically, and accept an explicit `# oracle: literal` comment as a documented escape — otherwise this rule has an irreducible false-positive risk and must ship as warning, not blocker, contradicting the table above only in initial severity; record as warning until a suppress-by-comment path exists. |
| `SSDOC-BIN-101` | evidence | blocker | yes | 40 | A binary/bit-table evidence block (`binary_oracle`/`capture_u64_le`-shaped call or a hand-authored `bit_table` capture) has no `layout_ref`/`layout:` argument naming a `BinaryLayoutRef`/production accessor, per research §6.1/§6.4's "the manual table is generated from the same layout used by the parser/comparator." | A purely illustrative fixture in a *design-mockup* doc (already required to be labeled as such by `SSDOC-EVD-105`/`SSDOC-MAN-101`) is out of scope for this rule — it only scans executable `.spl`, never `.md`. Within `.spl`, a binary literal used for something other than an evidence table (e.g. a magic-number constant in unrelated logic) must not trip this — scope strictly to calls matching the binary-evidence API surface, not any `[u8]`/hex literal. |
| `SSDOC-BIN-102` | evidence | warning | no | 20 | A binary evidence declaration has no explicit byte-order (`ByteOrder`) or bit-numbering (`BitOrder`) argument. | Single-byte fields (width ≤ 8 bits, no multi-byte field in the layout) have no endianness to declare; exempt layouts where every field's `width <= 8`. |
| `SSDOC-MAN-101` | maintainability | warning | no | 15 | A generated manual under `doc/06_spec/**` (or a hand-maintained example manual under `doc/07_guide/**`) has prose content with no matching span in the current source render — detected via `spipe-docgen`'s "source hash" marker: the manual's recorded source SHA-256 does not match a fresh hash of the named `.spl`, OR the manual has no such marker at all while claiming to be "generated." | A genuinely hand-authored *design* document that never claimed to be generated (no "Generated from" / source-hash line, explicitly labeled "design mockup" per §2's `SSDOC-EVD-105` disposition) must be exempt — gate strictly on documents that assert generated status, never on all Markdown under `doc/06_spec` or `doc/07_guide`. |

Severity/deduction/blocker values above are proposed, following the existing
catalog's pattern of weighting genuine-oracle-defeating findings
(EVD-102/104/107, BIN-101, PROTO-102) as blockers and structural-completeness
findings as warnings/advice — mirrored on `SSDOC-ORA-001/002` (blocker,
oracle-defeating) vs. `SSDOC-ORA-003` (advice, explainability). A later
implementation lane should treat these as a starting proposal subject to
calibration against a real corpus, per the existing `false_positive_limits`
convention of every current rule.

### 2.1 Not mechanically detectable — recorded, not specified as rules

Per the assignment's instruction, the following candidate findings from
research §9/§4 are **not** included above because no source-only or
single-run detection avoids an unacceptable false-positive rate:

- **"Screenshot pixel diff is meaningful vs. noise"** — whether a
  `pixel_threshold`/`pixel_diagnostic` comparison's tolerance is *appropriate*
  for the content is a domain judgment; a rule can check the tolerance is
  declared (already covered by requiring `reason`/tolerance metadata,
  general oracle-mode rules) but not that it is *correct*.
- **"TUI width-ambiguous content is handled correctly"** — noted under
  `SSDOC-TUI-101` above: presence of a width-profile declaration is checkable,
  correctness of that declaration against actual grapheme content is not,
  without executing full Unicode segmentation and manually judging the
  East-Asian-width policy choice — that is a review question, not a scan.
- **"Grammar/ABNF adapter accepts exactly the intended language"** — grammar
  correctness is undecidable from the spec file; only conformance/negative
  fixtures (already required by acceptance gates in the research doc §10)
  provide evidence, and fixture *coverage* is exactly `SSDOC-COV-001`
  (existing rule), not a new evidence-specific one.

---

## 3. New commands

All four commands are new subcommands/flags; none exist in `main.spl` today
(§1.3). Each must fail closed: an operational failure (bad path, unreadable
evidence manifest, unknown profile) is a nonzero exit with a diagnostic on
stderr, never a silent pass, matching the existing "empty scope is an
operational failure" convention (`sspec_documentization_maintenance.md:64-65`).

### 3.1 `sspec-maintain evidence <spec> --explain`

- **Args:** one `*_spec.spl` path (directory scope is out of scope for v1 —
  evidence is a per-run fact, not aggregable the way `scan` is). `--explain`
  is required in v1 (the bare `evidence <spec>` form is reserved for a future
  machine-readable dump; omitting `--explain` today is a usage error, exit 2).
- **Behaviour:** runs the spec's evidence capture/comparison path (this
  requires actually executing the scenario, not static parsing — see §1.3),
  loads the resulting `ComparisonResult`/`EvidenceManifest`, and for each
  `EvidenceCheckResult` prints: selector, mode, expected, actual, PASS/FAIL/
  IGNORED, and — for a FAIL — the specific fail-closed rule that fired
  (unresolved selector / ambiguous / closed-mode extra field / zero positive
  resolutions / etc., per `sspec_typed_evidence.md:121-129`).
- **Output shape (human):** one block per evidence id, one row per check,
  mirroring the QA verification tables already shown in the research doc
  (e.g. §5.5's table). **JSON:** array of `{evidence_id, profile_id, checks:
  [{selector, mode, expected, actual, status, reason}], manifest: {...}}`.
- **Exit codes:** `0` evidence present and every check PASS or IGNORED with a
  reason; `1` at least one check FAIL or a fail-closed rule fired; `2` no
  evidence declared in the spec, spec not found, or spec failed to execute
  (a crash during capture is not silently treated as "no evidence").
- **Fail-closed:** since this command *executes* the spec, a spec that only
  emits `pending-review` evidence (§3.4) must render those checks as
  `PENDING`, not `PASS` — `--explain` must never upgrade pending status.

### 3.2 `sspec-maintain verify-examples`

- **Args:** none required; optional `--root <dir>` (defaults to repo root)
  and `--manuals <glob>` (defaults to `doc/07_guide/**/*manual_example*.md`
  plus `doc/06_spec/**/*.md`).
- **Behaviour:** for every scanned manual, extract its named source spec
  path(s) (via the same "Generated from"/source-attribution convention as
  `SSDOC-EVD-105`/`SSDOC-MAN-101`, §2), then for each named path perform two
  checks in order: (a) **existence** — `Read`/stat the path; if absent, record
  a `MISSING_SOURCE` defect naming the manual and the path it claimed; (b)
  **fidelity** — if the path exists, re-run `documentize`/evidence capture
  against it and diff the manual's claimed evidence-block content
  (capture kind, field names, example values) against what the current
  source actually produces; a mismatch is a `STALE_OR_MISMATCHED_SOURCE`
  defect naming both the claimed and actual content.
- **Output shape:** one line per defect: `<manual path> :: <defect kind> ::
  <named spec path> :: <detail>`; `--format json` emits
  `[{manual, defect_kind, named_source, detail}]`. A clean run prints
  `verify-examples: N manuals checked, 0 defects` — never a silent empty
  success (mirrors the `check-tree-size-push.shs` verdict-line convention
  the repo already uses elsewhere for exactly this "vacuous pass" failure
  mode).
- **Exit codes:** `0` zero defects across all checked manuals; `1` any
  `MISSING_SOURCE` or `STALE_OR_MISMATCHED_SOURCE` defect found; `2`
  operational failure (no manuals matched the glob at all is treated as
  `ERROR`, not `PASS`, since an empty scan proves nothing — same
  fail-closed posture as the repo's push guards).
- **Fail-closed:** existence check (a) requires zero interpretation — a path
  either resolves on disk or it does not — so it has no false-positive risk
  and should be the first gate landed (§5). Fidelity check (b) is strictly
  harder (needs a defined "what does a manual claim" extraction convention)
  and may ship as advice-only until that convention is frozen.

### 3.3 `sspec-maintain scan <spec|dir> --profile-completeness`

- **Args:** existing `scan` positional arg (spec or dir) plus the new
  `--profile-completeness` flag; composes with existing `--format`,
  `--min-score`, `--deny-severity`, `--baseline`, `--suppressions` flags
  (`sspec_documentization_maintenance.md:39-47`) rather than replacing them.
- **Behaviour:** runs the normal `scan`, then additionally evaluates the
  evidence-specific findings from §2 that *are* statically detectable
  (EVD-101, EVD-103, EVD-105, EVD-106 file-existence half, UI-101, UI-102,
  TUI-101, PROTO-101, PROTO-102, BIN-101, BIN-102, MAN-101) and folds them
  into the same `SspecDocumentizationReport`/score. The four runtime-only
  rules (EVD-102, EVD-104, EVD-107, and the marker half of EVD-105) are
  *not* evaluated by `scan` even with this flag — they require executing the
  spec, which plain `scan` never does (`sspec_documentization_maintenance.md:214-217`:
  "Core scan... paths are local"; running the spec under test is a much
  larger scope change than this flag implies and is explicitly out of scope
  — `--profile-completeness` stays a static-only addition).
- **Output shape:** identical report shape as today's `scan`, with the new
  rule ids appearing in `findings[]` exactly like existing ones; `raw=`/
  `effective=` aggregate lines unchanged in format.
- **Exit codes:** unchanged from `scan` today — `--min-score`/
  `--deny-severity` govern pass/fail exactly as now; the new findings simply
  participate in scoring.
- **Fail-closed:** without `--profile-completeness`, behaviour is byte-for-byte
  identical to today's `scan` — this is strictly additive, so there is no
  regression risk to the existing 24-rule catalog's determinism.

### 3.4 `simple test <spec> --update-evidence` / `--accept-evidence`

- **Args:** existing `simple test <spec>` invocation plus exactly one of the
  two new flags (mutually exclusive; passing both is a usage error, exit 2).
- **`--update-evidence`:** runs the spec, captures fresh
  `RawArtifact`/`CanonicalEvidence`/`ComparisonResult`/`EvidenceManifest` for
  every evidence declaration, and writes/overwrites the golden artifact and
  manifest sidecar — but marks every touched manifest's `status` field
  `pending-review` (never `accepted`), per the assignment's explicit
  requirement that new/changed evidence "must not count as PASS until
  accepted." A `--update-evidence` run's own test-level exit code reflects
  whether the *update* succeeded (evidence captured without a crash), not
  whether the new evidence matches anything — there is nothing to compare
  against yet on first capture, and on a re-capture the prior golden is what
  changed, so PASS/FAIL against the old golden is meaningless here.
- **`--accept-evidence`:** does not run new captures; it takes the current
  `pending-review` manifest(s) for the named spec and flips `status` to
  `accepted`, requiring an explicit reviewer action (a human running this
  command) — never automatic. Refuses (exit 1) if any targeted manifest is
  incomplete per `evidence_manifest_is_complete` (`sspec_typed_evidence.md:159-161`)
  — an incomplete manifest cannot be accepted, since acceptance is exactly
  the claim that the manifest is trustworthy evidence.
- **Fail-closed core rule:** ordinary `simple test <spec>` (no flag) must
  treat any `pending-review` evidence check as **FAIL**, not PASS, not SKIP.
  This is the load-bearing guarantee the assignment asks for: a captured-but-
  unaccepted change cannot silently ride through CI as green. Only
  `--accept-evidence` can clear `pending-review`, and only for evidence that
  already passed its own comparator checks (accepting a FAILing manifest is
  a separate usage error, exit 2, distinguishing "I reviewed and approved a
  passing new baseline" from "I am hiding a failure").
- **Exit codes:** plain `simple test <spec>` — `0` all checks accepted+PASS,
  `1` any FAIL or any remaining `pending-review`; `--update-evidence` — `0`
  capture succeeded (regardless of comparison outcome), `1` capture itself
  errored (provider crash, unwritable artifact path); `--accept-evidence` —
  `0` all targeted manifests were complete+passing and are now accepted, `1`
  any targeted manifest was incomplete or failing, `2` no `pending-review`
  manifest found for the named spec (nothing to accept is an operational
  error, not a silent no-op success).

---

## 4. The example-integrity gate (`verify-examples`)

The three concrete 2026-08-08 defects, and how `verify-examples` (§3.2)
catches each mechanically:

| Manual | Named source | Defect | Detection path |
|---|---|---|---|
| `doc/07_guide/app/spipe/manual_examples/gui_web_manual_example.md` | `test/03_system/app/notes_web/notes_web_spec.spl` | Named spec **does not exist** on disk | Existence check (§3.2 step a): `Read`/stat the extracted path; absent → `MISSING_SOURCE`. Zero interpretation required — purely mechanical, no false-positive surface. |
| `doc/07_guide/app/spipe/manual_examples/statistics_manual_example.md` | `test/03_system/app/compiler_perf/warm_start_throughput_spec.spl` | Named spec **does not exist** on disk | Same existence check as above — identical mechanism, different manual. |
| `doc/07_guide/app/spipe/manual_examples/baremetal_network_manual_example.md` | `test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl` | Named spec **exists**, but describes CQE phase-bit / CC-register-bitfield / NVMe-TCP-capsule evidence while the actual spec covers emulated NAND write/read + FTL migration — a fidelity mismatch, not an absence (research §2.2, line 76-77: "the manual itself discloses this at lines 8–10") | Fidelity check (§3.2 step b): the manual's claimed evidence content (field names: CQE phase bit, CC register bits, NVMe/TCP capsule PDU) is extracted from the manual's evidence-block markers and diffed against what `documentize`/evidence capture actually produces from the named spec (NAND CLI output, hand-written text captures — no CQE/register/capsule fields at all). A diff with zero overlapping field names between claimed and actual evidence content is the mechanical signal; this is harder than existence and requires the marker-extraction convention noted as a prerequisite in §2's `SSDOC-EVD-105`/`SSDOC-MAN-101` rows. Until that convention is frozen, this specific defect is still catchable by a narrower rule: the manual **already discloses the mismatch in its own prose** ("lines 8–10" per the research audit), so an interim mechanical check — flag any manual whose body contains hedging language adjacent to its source-attribution line (e.g. "does not yet exist", "conceptual", "for illustration") — closes this specific instance immediately, while the general fidelity diff is built. |

This shows why existence (defects 1–2) ships first and unconditionally, while
general fidelity (defect 3) needs the extraction convention built first — the
interim self-disclosure heuristic is a stopgap for the one instance we know
about, not a substitute for the real diff.

---

## 5. Implementation plan

| Order | Change | Module | Deliberate-red fixture required before trusted |
|---|---|---|---|
| 1 | Freeze the marker/attribution convention: how a manual declares "generated from `<path>`, sha `<hex>`" and how an evidence block is delimited for extraction. Blocks everything downstream in §2/§3/§4 that reads manual content. | new: `doc/04_architecture/infra/sspec/evidence_manual_markers.md` (design-only, out of this document's scope to write) | N/A (a convention, not a detector) |
| 2 | `verify-examples` existence check only (§3.2 step a) | new `src/app/sspec_maintain/verify_examples.spl` + `main.spl` dispatch branch | A manual naming a deliberately deleted/renamed spec path must report `MISSING_SOURCE`; a manual naming a real path must report zero defects. Use the two real 2026-08-08 instances (§4) as the initial fixture pair — they are already known-red. |
| 3 | Catalog entries for the ten statically-detectable rules (EVD-101/103/105-existence-half/106-hash-half, UI-101/102, TUI-101, PROTO-101/102, BIN-101/102, MAN-101) | `rules.spl` (append to `sspec_rule_definitions()`) | Each rule needs one fixture `.spl`/`.md` pair that trips it and one adjacent "looks similar but must not trip" pair per its false-positive-limits column in §2 — e.g. PROTO-102 needs both a `check_exact(".*")` positive fixture and a `check_exact` on a field whose real value legitimately contains `.*` with the `# oracle: literal` escape, proving the escape suppresses it. |
| 4 | Detection producers for the same ten rules, wired into the existing scan pipeline behind `--profile-completeness` | new `src/app/sspec_maintain/evidence_facts.spl` (mirrors the existing `source_facts.spl` pattern) + `analyzer.spl` wiring + `main.spl` flag plumbing on `_run_scan` | Full scan-level fixture: a directory containing one file per rule that should fire and one file per adjacent non-firing case; assert the fired set matches exactly the expected rule-id set, catching both false negatives and false positives in one run. |
| 5 | `sspec-maintain evidence <spec> --explain` (§3.1) | new `src/app/sspec_maintain/evidence_explain.spl` + `main.spl` dispatch branch | A spec with one PASS check, one FAIL check (selector resolves to wrong value), and one IGNORE check with a reason; `--explain` output must show all three with correct status and the FAIL must name its fail-closed rule. |
| 6 | `simple test <spec> --update-evidence` / `--accept-evidence` (§3.4) — the largest change, touching the `simple test` runner, not `sspec-maintain` | test-runner evidence-manifest plumbing (module not yet located; out of `sspec_maintain`'s tree entirely — a later lane must locate the runner's result-aggregation point) | Three-stage fixture: (a) fresh capture via `--update-evidence` leaves manifest `pending-review` and plain `simple test` on that spec still exits 1; (b) `--accept-evidence` on a passing pending manifest flips status and plain `simple test` now exits 0; (c) `--accept-evidence` on a FAILing pending manifest is refused, exit 1, and plain `simple test` still exits 1 — proving acceptance cannot launder a failure. |
| 7 | `verify-examples` fidelity check (§3.2 step b) once the marker convention (step 1) is frozen | extend `verify_examples.spl` | The known-red NVMe/NAND mismatch (§4, defect 3) as the positive fixture; a manual whose claimed and actual evidence field names fully overlap as the negative (must-not-fire) fixture. |
| 8 | `scan --profile-completeness` for the four runtime-only rules (EVD-102/104/107, EVD-105 marker-half) — requires executing the spec from within `scan`, a scope change flagged as open in §3.3 | design decision needed first: does `scan` gain an execute-the-spec mode, or does this stay `evidence --explain`-only forever | Not orderable yet; recorded as blocked on a design decision, not scheduled. |

Steps 2–3 can run in parallel (independent modules); step 4 depends on both.
Step 5 is independent of 2–4 and can run in parallel with them. Step 6 is the
riskiest — it touches the test runner's pass/fail semantics directly, which
the "fail-closed core rule" in §3.4 makes load-bearing for the whole
assignment's goal (unaccepted evidence must not read as PASS) — so it should
not start until step 5's manifest-reading code is proven correct, since step
6 reuses that same manifest-status logic to gate `simple test`'s own exit
code.

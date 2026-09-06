# Schema collision: foundry doc's "missing" Observation/Hypothesis/Experiment vs. landed `bug_*` tables

**Status:** naming collision, not a real gap. Do not implement.

## The claim (design doc, unverified against this repo)

`doc/01_research/infra/spipe/spipe_skill_foundry_debug_training.md` §2.2
(~L88-104) asserts the current debug material lacks "typed observations,
hypotheses, experiments, or causal claims" and proposes new types
`ObservationV1` / `HypothesisV1` / `ExperimentProposalV1` (§6.3, ~L314-343).

## Why it's wrong for this repo

`doc/01_research/infra/spipe/spipe_bug_management_debug_knowledge_evidence.md`
§6.2 already landed this as `bug_observations`, `bug_hypotheses`,
`bug_experiments` (plus `bug_scenarios`, `bug_artifacts`, `bug_fingerprints`,
`bug_environments`) — same concepts, already named, already speced as part of
"Bug textual database V2" (§6). The foundry doc's audit in §2.1 lists what
SPipe/Simple already contain but does not appear to have cross-checked against
that companion doc's §6.2 table before concluding the concepts are missing.

## Which naming wins

**The landed one** (`bug_observations` / `bug_hypotheses` / `bug_experiments`
/ `bug_scenarios`). Per `.claude/rules/code-style.md` and the repo's
no-numbered-module-splits rule, do **not** create a parallel `*V1` type family
— that would be exactly the duplicate-module pattern the rules forbid.

## Fields the foundry doc has that the landed tables genuinely lack (worth merging)

Checked field-by-field against `bug_hypotheses`, `bug_experiments`,
`bug_scenarios`, `bug_artifacts` in the landed doc's §6.2:

- **`reproduction_level`** — `bug_scenarios` already has "reproduction level"
  as a field. Not missing. (Foundry doc's claim of novelty here does not
  hold.)
- **Sealed `prediction` before execution** — `bug_hypotheses` already has
  `predicted observations`, and `bug_experiments` already has `expected
  discriminating outcomes`. The *value-add* from the foundry doc is making the
  ordering explicit (predict, seal, then run) as a checklist step, not a new
  field — added to `.claude/skills/lib/debug_ladder.md` "Sealed prediction".
- **`parser_uid` / `parser_version`** as separate fields — genuinely new.
  `bug_artifacts` only has "parser status and receipt" (a status/receipt pair,
  not an identified parser version). Worth merging into `bug_artifacts` if a
  case ever needs to distinguish "this dump was parsed by parser X v3" from
  "this dump was parsed by parser Y v1" for reproducibility.
- **`trust: untrusted|quarantined|verified`** tri-state — genuinely new.
  `bug_artifacts` has "redaction status" and "encryption/classification" but
  no explicit trust-provenance tri-state distinct from those. Worth merging.
- **`derived_from[]`** explicit lineage list — genuinely new. `bug_artifacts`
  has no field tracking that one evidence item was derived from another
  (e.g., a normalized log derived from a raw capture). Worth merging.

## Recommendation

No code change needed now. If/when `bug_artifacts` is next revised, add
`parser_uid`, `parser_version`, `trust`, and `derived_from[]` to it rather than
adopting `EvidenceItemV1`. Everything else in the foundry doc's §6.3/§6.4/§6.5
schemas is already covered by the landed `bug_*` tables under different names.

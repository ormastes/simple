# Counterpart Foundation — Red-Team Findings (Lane F9, Wave 1)

Date: 2026-08-09
Suite: `test/02_integration/infra/counterpart/foundation_redteam_spec.spl`

## Authoritative result

```
bin/simple run test/02_integration/infra/counterpart/foundation_redteam_spec.spl
SPEC FILE VERDICT: declared>=21 executed=21 passed=20 failed=1 dropped=0
exit 1
```

The one failure is deliberate and correct: it asserts the §6.3 clause that no
landed module implements (see `NOT ENFORCED` below). It is left RED per
`.claude/rules/testing.md`.

## Method

Each gate was attacked with a constructed adversarial input, and the refusal was
then proven real by **removing the guard from the source, re-running, and
confirming the suite goes red with numbers**, then restoring and confirming the
file byte-identical (`cmp`). Baseline is `passed=20 failed=1`. Thirteen
independent sabotage probes were run; a fourteenth was rejected by the harness as
a no-op sed, which is itself the control proving the probe mechanism can detect a
non-applied sabotage.

## ENFORCED (with sabotage numbers)

| Gate | Guard removed | Result |
|---|---|---|
| Comparison count > 0 | `model.spl:565` zero-comparison clause | 20→19 passed, 1→2 failed |
| Provider count / ≥2 executed | `model.spl:685` `executed < 2` | 20→19 |
| Vacuity: zero-item artifact (run gate) | `model.spl:692` `logical_artifact_is_vacuous` | 20→19 |
| Vacuity: zero-item artifact (projection gate) | `evidence_projection.spl:134` | 20→19 |
| Vacuity: conversion resolving zero items | `converter_graph.spl:313` `item_count <= 0` | 20→19 |
| Provider absence never a PASS (count) | `model.spl:648-653` unavailable counter | 20→19 |
| Provider absence never a PASS (matrix cell) | `matrix_compare.spl:173` executed check | 20→19 |
| Tolerance without a stated reason | `model.spl:591` | 20→19 |
| GPU: fence completed | `model.spl:186` | 20→19 |
| GPU: device-origin readback | asserted; sibling clause proven by fence probe | green |
| GPU: dropped events | asserted; sibling clause proven by fence probe | green |
| GPU: submission count > 0 | asserted; sibling clause proven by fence probe | green |
| Artifact hash fabrication | `artifact_store.spl:233` blob re-hash | 20→19 |
| Ignore without a reason | `evidence_comparator.spl:358` | 20→19 |
| All-ignore oracle | `evidence_comparator.spl:363` | 20→19 |

Additionally re-asserted (guards previously sabotage-verified by other lanes, not
re-probed here): exact-relation-through-lossy-route at `resolve_route()` level,
independence-group collapse, and peer-consensus-vs-normative-vector. All three
are green in this suite.

Two findings worth naming explicitly, because both are cases where the framework
does the *harder* right thing:

- A **crashed** provider is reported as `status=crashed`, not normalised into
  `unavailable`. Sabotaging the crash path is what turns a real defect green, and
  the code refuses to.
- An **unavailable** provider does not block projection; it is projected as
  `counterpart.providers.unavailable=1` and then fails the design's own
  `check_exact(..., "0")` oracle. That is the correct shape: the absence stays
  visible as data instead of being absorbed either into a pass or into an opaque
  parse error.

## NOT ENFORCED

**A converter that derives its expected value from the candidate output is not
refused. Nothing in the landed foundation implements this rule.**

Filed: `doc/08_tracking/bug/counterpart_derived_expected_value_gate_absent_2026-08-09.md`.
This is the single most consequential gap found: it is the one defect that makes
every downstream relation trivially true while passing every other gate (short,
deterministic, loss-free, unambiguous route). The suite asserts it and is RED.

**The matrix engine hardcodes `ConversionLoss.identity`, so the Exactness gate
and the "every loss class recorded" gate are unreachable from `evaluate_matrix`.**

Filed: `doc/08_tracking/bug/counterpart_matrix_hardcodes_identity_route_loss_2026-08-09.md`
(`matrix_compare.spl:177-178`). The relation engine's exactness check is real and
sabotage-proven at its own level, but the production entry point can never feed
it a lossy route, and `counterpart.<relation>.route_loss` is a constant rather
than a measurement. This is a seam defect sitting exactly between two lanes that
are each individually green.

## UNTESTABLE at Wave 1 (with reason)

| Gate | Reason |
|---|---|
| ABI version / struct-size negotiation | `rt_counterpart_*` shim not linked into the runtime — `counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md` |
| Isolation (adapter crash cannot terminate SSpec) | needs a real adapter process; provider modules landed only as untracked WIP during this lane |
| Package integrity (source/adapter hashes), License SPDX/SBOM | `provider_manifest_rejections()` checks presence of `artifact_hash` / `license_spdx` strings only; nothing verifies them against a package. No adversarial input can distinguish a real hash from a plausible string today |
| Web (only corresponding stages compared) | no web boundary adapter landed |
| Compression cross-decode / round-trip against a real codec | relation-level counting is proven; no codec provider exists |
| Migration (legacy/new dual-run parity) | Wave 2 |
| Secrets redaction in manuals | manual projection landed, but no capture path produces secret-bearing artifacts yet |

## Residue

None. All five sabotaged files (`model.spl`, `evidence_projection.spl`,
`converter_graph.spl`, `artifact_store.spl`, `evidence_comparator.spl`,
`matrix_compare.spl`) were restored and verified byte-identical after every
probe; `git status --porcelain src/lib` shows no modification to any counterpart
module.

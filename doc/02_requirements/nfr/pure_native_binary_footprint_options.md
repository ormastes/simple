<!-- codex-research -->
# Pure-native binary footprint — NFR options

Status: **UNSELECTED OPTIONS — not for integration.**  These options reconcile
with the already-selected `runtime_optional_provider_binary_size_optimization`
contract.  In particular, **all admission size/startup/RSS cohorts use at least
30 development samples and 100 release samples**.  The 15-sample line in
`901b3fa290c` is exploratory-only and is not admissible.

## Common evidence floor

For each control/candidate/comparison row, retain source revision and source
state digest; compiler/provenance, target, toolchain, argv, allowed environment,
and cache-policy identity; exact immutable input/runtime/provider/workload/link
manifest paths and digests; primary/provider/runtime-closure/installed-total
bytes; load-segment rows; canonical dynamic dependency identities; map/section/
symbol evidence; raw samples and evaluator policy digest; timeout/output/result
budgets; and final PASS/FAIL/INCONCLUSIVE/UNAVAILABLE reason.  File-backed,
private-dirty, and maximum RSS are distinct fields.  Missing authority, dirty
mismatch, fallback, crash, timeout, truncation, or unbounded result is never a
pass.  A pair-level admission receipt binds source-matched control and candidate
receipts plus profile/workload manifests and carries an individual verdict for
each selected NFR.

## N-1 — Compatibility cohort and existing absolute gates

Retain the selected runtime-optional NFRs as the admission target: same-host
NoGC hello below 2 MiB; Linux ELF `release-small` NoGC hello at most 15 KiB and
at most 1.05× the same-toolchain C baseline; target-specific admitted format
allowance elsewhere; no optional provider for no-import hello; and startup/RSS
within the selected Python comparison allowance.  Require the common evidence
floor and 30/100 cohort.

- Pros: preserves the only already-selected measurable target; reuses the
  existing cohort verifier; prevents a documentation-only feature from quietly
  relaxing the performance contract.
- Cons: stringent targets may first expose unrelated closure regressions; some
  targets need a separately admitted format allowance.
- Effort: M — roughly 12–22 files (receipt evolution, producer/checker,
  fixtures, tests, and requirement traceability).

## N-2 — Relative control admission with no new absolute size promise

Require same-source, same-toolchain, same-profile controls and a smaller primary
artifact for every claimed optimization.  Report provider, runtime closure, and
installed totals without hiding a moved library; retain idle provider-map and
RSS/startup non-regression gates.  Keep the existing 30/100 cohort but defer any
new absolute target until F-1 produces an owner-issued baseline.

- Pros: safest when baseline provenance is incomplete; detects regressions while
  avoiding invented numeric goals; accurately describes split-versus-removal.
- Cons: can approve a small primary-file reduction while installed total grows;
  does not by itself enforce the selected 15 KiB/2 MiB expectations unless
  paired with N-1.
- Effort: S–M — roughly 8–16 files (comparison policy, receipt, checker,
  fixture, and tests).

## N-3 — Hybrid: selected absolute gates plus strict closure attribution

Adopt N-1 and add N-2's same-source control requirement, with explicit
additional limits: no unexpected dynamic dependency, zero compiler-provider
images/workers for help/version/non-build commands, and separate file-backed,
private-dirty, and max-RSS reporting.  A Stage4 dynamic-runtime candidate may
be measured only against a source-matched exact-static control and cannot become
the product default from a passing receipt alone.

- Pros: strongest auditability; makes optimized-file, installed-footprint, and
  resident-memory claims distinguishable; aligns exact closure with selected
  optional-provider behavior and the 30/100 contract.
- Cons: greatest schema/test and platform-normalization cost; requires careful
  evaluator versioning to avoid false comparability.
- Effort: L — roughly 20–34 files (all N-1/N-2 work plus closure/dependency and
  RSS attribution, admission tests, and platform fixtures).

## Selection note

N-1 preserves the existing target verbatim, N-2 is a provenance-first interim
policy, and N-3 combines both.  Select one alongside F-1/F-2/F-3; do not carry
the unselected `901b3fa290c` “15 fresh processes” threshold into final NFRs.

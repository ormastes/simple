# Diagnosis: `check-test-tree-divergence.shs` FAIL — 982 diverged (2026-08-08)

**Status:** diagnosis only, nothing changed. Baseline file, guard script, and
test files were not touched.

## 1. What the guard measures

`scripts/check/check-test-tree-divergence.shs` compares two mirrored
directory pairs byte-for-byte:

- `unit`: canonical `test/01_unit/` vs shadow `test/unit/`
- `integration`: canonical `test/02_integration/` vs shadow `test/integration/`

For every `*.spl` file under the **shadow** dir (excluding
`.spipe_matchers_*` / `.sspec_wrapped_entry_*`), it computes the same
relative path under the **canonical** dir. If the canonical file doesn't
exist, the pair is silently skipped (`continue`) — it is out of scope, not
counted as identical or diverged. If both exist, `cmp -s` decides identical
vs diverged. "Diverged" therefore means **byte-for-byte content mismatch**,
not presence/absence, not a hash, not a semantic diff — a single differing
byte anywhere in the file (including comments/whitespace) counts as
diverged.

Baseline: `scripts/check/test_tree_divergence_baseline.txt`, one
`label:relpath` line per known-diverged pair as of 2026-08-08. The guard is
baseline-relative (like a git-blame-clean lint):

- **"N new"** = pairs that diverge NOW but are NOT in the baseline
  (`comm -23 current baseline`) — a regression signal.
- **"N fixed-but-still-baselined"** = pairs that ARE in the baseline but do
  NOT appear in the current diverged list (`comm -13 current baseline`). The
  guard's own message calls these "now IDENTICAL", but that is only one of
  two possible causes — see §3 below, this is imprecise wording, not a bug
  in the comparison logic itself.

Verbatim run (`sh scripts/check/check-test-tree-divergence.shs`):

```
check-test-tree-divergence: 5724 pairs compared, 4742 identical, 982 diverged
check-test-tree-divergence: baseline has 982 known-diverged entries
check-test-tree-divergence: diverged-path list written to /tmp/test_tree_divergence_current.txt
check-test-tree-divergence: NEW divergence(s) not in baseline:
  + unit:lib/common/math_comprehensive_spec.spl
check-test-tree-divergence: baseline entries that are now IDENTICAL (baseline is stale — remove these lines from .../test_tree_divergence_baseline.txt):
  - unit:app/interpreter/mailbox_spec.spl
check-test-tree-divergence: FAIL — 982 diverged vs 982 baselined (1 new, 1 fixed-but-still-baselined)
```

## 2. "1 new": `unit:lib/common/math_comprehensive_spec.spl` — real, intentional (a)

`diff test/01_unit/lib/common/math_comprehensive_spec.spl
test/unit/lib/common/math_comprehensive_spec.spl` shows the canonical copy
has **26 extra lines** the shadow copy lacks: a new `use std.math.{math_pow,
math_cbrt}` import plus a whole new `describe "Math re-exported from
std.common.math"` block (3 `it` examples) guarding against a facade-shadowing
regression.

`git log -3` on the canonical path shows the top commit is
`513c26528b5 test(lib): gate the std.math re-exported surface against
re-shadowing` — the shadow copy's last touching commit is the older
`cfe0506e336`. This is a genuine, deliberate edit landed on the canonical
tree only and never mirrored to the shadow tree. **Verdict: real new
divergence, not an artifact.** It needs either (i) the same block copied
into the shadow file (reconciliation), or (ii) deliberate accept-as-baseline
if the shadow tree is being phased out. Either way this is legitimate
guard behavior working as designed — not a false positive.

## 3. "1 fixed-but-still-baselined": `unit:app/interpreter/mailbox_spec.spl` — tooling artifact (c), not "now identical"

`test/01_unit/app/interpreter/mailbox_spec.spl` **does not exist** — `ls`
returns "No such file or directory", and it is absent from `origin/main`
too. `test/unit/app/interpreter/mailbox_spec.spl` **does exist**, containing
an old 4-line pending stub (`"function 'Mailbox.default' not found in
interpreter runtime"`).

`git show 983058c5ff3 --stat` (`fix(lib): delete dead struct Mailbox,
unblock Stage-2 ambiguous-export build`, 2026-08-07) explicitly deleted the
canonical file as "duplicate of" `test/01_unit/lib/nogc_async_mut/
mailbox_spec.spl` (which was rewritten in the same commit) — but did **not**
touch the shadow copy under `test/unit/app/interpreter/`.

Because the guard's loop is `[ -f "$canon_file" ] || continue`, once the
canonical file is gone the pair is no longer compared at all — it drops out
of `current_diverged` for the same reason a truly-reconciled pair would,
and the diff logic (`comm -13`) cannot distinguish "now byte-identical" from
"no longer comparable because one side was deleted". **Verdict: this is a
guard wording/logic gap, not a content regression and not a real
reconciliation.** The shadow file is now an orphan (dead stub content with
no canonical counterpart) — the correct action is almost certainly to
delete the orphaned shadow file (mirroring the same "duplicate, delete"
reasoning as commit 983058c5ff3), not to silently drop the baseline line as
if the divergence were resolved by content matching.

## 4. Systemic vs independent verdict for the 982: **independent, not systemic**

Evidence against a single systemic cause:

- **No missing-file artifact hiding in the 982.** Checked all 982 current
  entries: `missing_canon=0 missing_shadow=0` — every pair has both files
  present, so the mailbox-style "one side deleted" issue is isolated to the
  1 "fixed" case, not a hidden bulk pattern.
- **No whitespace/line-ending false-positive class.** Sampled 16 pairs
  (every 65th line, spanning both `unit` and `integration`) and compared
  `diff` output with and without `-b -w` (ignore whitespace): line counts
  were identical in 15/16 cases (one showed 10 vs 8, a 2-line real
  whitespace-adjacent diff, not the bulk of the difference). So this is not
  systemically a CRLF/trailing-space/generated-timestamp artifact.
- **Wide, non-uniform diff magnitude.** Sampled diff sizes ranged from 2
  changed lines (`app/ui/widget_modifiers_spec.spl`,
  `compiler/codegen/baremetal_method_dispatch_spec.spl`) up to 1039 changed
  lines (`app/formatter/formatter_comprehensive_spec.spl`) and 112
  (`app/app_mcp_intensive_spec.spl`). A single systemic cause (e.g. one
  directory compared against itself with a path-prefix bug, or a
  code-generator stamping every file identically) would produce a uniform
  diff shape across files; this does not.
- **Matches the prior audit's finding.** The originating report
  (`doc/09_report/infra/duplicate_test_tree_divergence_audit_2026-08-08.md`,
  referenced in the guard's own header comment) already characterized these
  982 pairs (891 unit + 91 integration — matches this run's label split
  exactly: `891 unit`, `91 integration`) as genuinely independent content
  drift, including a documented case of **contradictory assertions on the
  same behavior** between the two copies
  (`os/kernel/loader/app_registry_spec.spl: len()==19 canonical vs ==18
  shadow`).

**Confidence: high.** The 982 is the accumulated byte-for-byte drift of two
long-lived duplicate test trees (`test/01_unit`+`test/unit`,
`test/02_integration`+`test/integration`) that are edited independently by
different sessions/commits over time, not one bulk artifact.

## 5. Recommended next action

- **Do NOT blanket re-baseline.** Re-running `--generate-baseline` would
  both silently accept the real new divergence in §2 and permanently erase
  the §3 orphan from tracking without fixing its root cause.
- **§2 (math_comprehensive_spec.spl):** needs manual review/reconciliation —
  port the `std.math` re-export regression-gate block from
  `test/01_unit/lib/common/math_comprehensive_spec.spl` into
  `test/unit/lib/common/math_comprehensive_spec.spl` (or explicitly decide
  the shadow tree doesn't need this guard), then drop the line from the
  baseline as a real fix.
- **§3 (mailbox_spec.spl):** delete the orphaned
  `test/unit/app/interpreter/mailbox_spec.spl` (stale stub with no canonical
  counterpart, same "duplicate of nogc_async_mut/mailbox_spec.spl" reasoning
  already applied to the canonical side in commit 983058c5ff3), then remove
  the baseline line — this is a real fix, not a re-baseline-to-hide-drift.
- **The remaining ~980 baselined pairs:** each represents real, independent
  content drift and requires per-file review to reconcile or intentionally
  diverge; no shortcut (bulk copy, bulk re-baseline) is safe given the
  documented contradictory-assertion case.
- **Guard improvement (not applied here, out of scope for diagnosis):**
  distinguish "pair now byte-identical" from "pair no longer comparable
  because one side was deleted" in the `comm -13` reporting — the current
  "now IDENTICAL" wording is factually wrong for the deleted-canonical case
  and could cause a future reviewer to skip actually deleting the orphan.

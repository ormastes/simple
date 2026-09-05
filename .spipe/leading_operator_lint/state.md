# leading_operator_lint — LEADOP001 interim guard

**Status:** DONE (rule landed in working copy, not committed)
**Date:** 2026-07-28
**Bug:** `doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md`

## What

The Rust seed parser glues a statement-leading `-`/`+` line onto the previous
statement as a binary operator when no DEDENT separates them. `return 15` ⏎
`-1` becomes `return (15 - 1)` → 14, and the tail expression vanishes so the
fall-through returns nil. The parser fix is deferred (in-flight work in that
directory + forces a seed rebuild); this lint is the agreed interim guard.

## Deliverables

| Path | Role |
|---|---|
| `src/compiler/35.semantics/lint/leading_operator.spl` | the rule (new file) |
| `src/compiler/35.semantics/lint/__init__.spl` | `export leading_operator.*` |
| `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` | `use` + `check_leading_operator_spl` + call |
| `build/leadop_proof/*.spl` | 6 both-direction fixtures |
| `build/leadop_sites.txt` | 276 sites grouped by tree, for the follow-up lane |

Backup: `/tmp/leadop_backup/leading_operator.spl`.

## Indent boundary

| class | seed behaviour | reported |
|---|---|---|
| candidate indent **==** previous statement | glued, silently wrong | **yes — LEADOP001** |
| candidate indent **>** previous statement | intended continuation feature | no |
| candidate indent **<** previous statement | DEDENT breaks the glue; correct | no |

The lesser-indent class was **measured, not assumed**: 1044 in-tree sites,
canonically a `while`/`if` block followed by a dedented bare `-1` tail
(e.g. `src/lib/log.spl:269`). Bug-doc truth-table cases D and M prove those
evaluate correctly. Reporting them would have buried the 276 real hazards under
79% noise — the exact false-positive flood that gets a rule switched off.

Also excluded: `return -1`, `(-1)`, `val z = -1`, `->`, `-=`/`+=`, `#`/`@`
lines, `"""` docstring bullets, and lines continuing an already-open expression
(previous line ends with an operator, comma, open bracket, or `:`).

## Severity: Warn (not Deny)

Deliberate. It is a silent-wrong-answer hazard, which argues for Deny, but 276
existing sites (144 outside `test/`) would fail the build the moment it landed.
Escalating a rule to Deny while its population is unconverted is what made lint
unusable earlier today. **Escalate to Deny only after `build/leadop_sites.txt`
is drained**, at which point the count is zero and Deny costs nothing.

## Proof

| fixture | expected | got |
|---|---|---|
| `bad_same_indent.spl` | flag | LEADOP001 at line 3 |
| `good_deeper_continuation.spl` | silent | silent |
| `good_dedent_tail.spl` | silent | silent |
| `good_return_neg.spl` (`return -1`) | silent | silent |
| `good_paren_neg.spl` (`(-1)`) | silent | silent |
| `good_docstring_bullets.spl` | silent | silent |

## Follow-up lane

1. Drain `build/leadop_sites.txt` — **not** a bulk sed; each site needs parens
   or an explicit `return`. Priority: `src/os/kernel/net/embedded_certs.spl`
   (kernel TLS trust anchors, hex decoder reading `f`/`F` as 14), then the rest
   of the ~20 hex decoders.
2. Fix the seed parser once its directory is quiet.
3. Then flip LEADOP001 to Deny.

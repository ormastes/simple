# The silent-default / fail-open lint (W-MC-DEF-001/002/003)

**Status: WARNING today. Promotion to a hard error is one line — see
[Promoting to an error](#promoting-to-an-error).**

Mission-critical code must not substitute a plausible-looking constant for an
answer it failed to compute. A crash is recoverable; a fabricated value
propagates as if it were real data. Until this rule landed, `mission_critical`
was a **directory label with no enforcement behind it** — nothing in the
compiler, the linter, or any guard read it. This is the first thing that makes
it mean something.

| Code | What it flags | Scope |
|---|---|---|
| `W-MC-DEF-001` | in-domain constant default on a lookup/resolution result | tree-wide |
| `W-MC-DEF-002` | `.ok()` discarding an error and continuing | mission-critical only |
| `W-MC-DEF-003` | vacuously-true success predicate (`failed == 0` alone) | mission-critical only |

Rule: `src/compiler/35.semantics/lint/silent_default.spl`
Guard: `scripts/check/check-silent-default-baseline.shs`
Specs: `test/01_unit/compiler/lint/silent_default_{reproducer,detection}_spec.spl`

## The defect this models

`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:288` resolved a struct
field index with `.unwrap_or(0)`. When resolution failed, every field read field
0's slot:

```
struct W3: first: i64, length: i64, tag: i64
make(3) -> W3(first: 9, length: n, tag: 77)
prints: first=9 length=9 tag=9
```

It blocked the bootstrap six times before anyone looked at the `unwrap_or`.

## The discriminator: in-domain vs out-of-domain

`.unwrap_or(<const>)` is *usually fine*. It is a defect only when the constant is
**indistinguishable from a legitimate result**:

```simple
trimmed.index_of("(").unwrap_or(0)     # DEFECT — 0 is a VALID index, so
                                       # "no paren" becomes "paren at col 0"
trimmed.index_of("(").unwrap_or(-1)    # SAFE — -1 is outside the index domain,
                                       # so every caller is forced to test it
```

So the rule flags in-domain constants (`0`, `1`, `true`, `""`, and
`unwrap_or_default()`) on lookup/resolution receivers, and deliberately stays
silent on `-1`. It also ignores non-lookup receivers: `cfg.port_setting()
.unwrap_or(8080)` is a genuine default, not a guess.

Measured on this tree (2026-08-17): **146** `.unwrap_or(<const>)` sites, **46**
on a lookup-shaped receiver, **13** already using the safe `-1` sentinel, and
`W-MC-DEF-001` fires on **one** — which is a real fail-open. A rule that fired on
all 146 would be switched off within a week.

## Scope: path convention **and** an opt-in marker

Path scope alone would be vacuous — the five files under
`src/lib/**/mission_critical/**` contain zero `unwrap_or` and zero `.ok()`, so a
purely path-scoped rule could never fire on today's tree. Mission-critical scope
is therefore the union of:

- a path containing `/mission_critical/`, and
- a file declaring `@mission_critical` near the top.

`@mission_critical` is **inert**: the compiler never parses it, it changes no
codegen, and only this text scan reads it. It exists so a module can opt in ahead
of the directory convention. This mirrors the two existing mission-critical rules
(`bare_primitive_internal`, `unwrapped_foreign_resource`) rather than introducing
a parallel mechanism.

`W-MC-DEF-001` is exempt from that scoping and runs tree-wide, because it is
sharp enough that scoping it would only hide real defects.

## Suppression

```simple
val idx = s.index_of("(").unwrap_or(0)  # lint:allow(silent_default) caller
                                        # already tested contains("(")
```

The marker must carry a **non-empty reason**, on the finding's own line or the
line immediately above. A bare `# lint:allow(silent_default)` with no text does
**not** suppress: an escape hatch with no reason is just a disabled rule spelled
differently. Audit every suppression in the tree with:

```bash
/usr/bin/grep -rn 'lint:allow(silent_default)' src/
```

## The baseline guard

`bin/simple lint` costs ~11.7s startup plus a per-declaration cost that is
superlinear in declaration content (see `.claude/rules/commands.md`), so gating a
push on a full-tree lint is not possible. `check-silent-default-baseline.shs` is
a fast grep **mirror of W-MC-DEF-001 only**, run over the whole tree in about a
second, baselined so it fails on new sites only — the pattern of
`check-no-phantom-module-imports.shs`.

```bash
sh scripts/check/check-silent-default-baseline.shs
# PASS — 75 candidate(s) checked, 0 new fail-open (baselined: 1)

sh scripts/check/check-silent-default-baseline.shs --selftest
sh scripts/check/check-silent-default-baseline.shs --generate-baseline  # reviewed changes only
```

Verdict is always the last line of stdout; `PASS` exit 0, `FAIL` exit 1,
`ERROR — nothing was checked` exit 2. A run that examined zero candidates is an
ERROR, never a pass. The selftest (7 fixtures) is fatal and runs before every
scan.

The mirror can drift from the `.spl` rule. The selftest fixtures are the same
cases the specs assert, so a divergence surfaces as a fixture disagreement rather
than silently.

## Promoting to an error

Change exactly one line in
`src/compiler/90.tools/lint/_LintMain/config_and_model.spl`:

```simple
levels["silent_default"] = "warn"   ->   levels["silent_default"] = "deny"
```

Nothing in `silent_default.spl` changes, and nothing in `lint_checks.spl`
changes. `silent_default_reproducer_spec.spl` asserts the current value, so the
spec tells you the moment it flips.

**Prerequisite:** `check-silent-default-baseline.shs` must report a baseline of
**0**. Today it is 1 (`erlang.spl:52`). Escalating a rule ahead of its population
is what made lint unusable the last three times — `raw_rt_access` and
`leading_operator` both carry the same note for the same reason.

## Known gaps

- The rule is a **text heuristic**, not a typed-HIR walk. `resolve(x)
  .unwrap_or(0)` split across two lines is missed. The upgrade path is the same
  as `bare_primitive_internal`'s: a typed-HIR walk.
- **Recall is deliberately narrow.** `d.get_value().unwrap_or(1)` feeding a
  dimension product is a plausible fail-open that this rule does *not* flag,
  because `get_value` is not lookup-shaped. Widening the receiver set trades
  precision for recall; do it with measurements, not by intuition.
- The rule lints `.spl` only. The motivating defect was in **Rust seed** code
  (`access.rs`), which `bin/simple lint` does not read. 1,356 `.unwrap_or`
  sites under `src/compiler_rust/**/*.rs` are outside this rule's reach; a
  clippy lane would be the counterpart.
- Item 6 of the original brief — shell fail-open (`|| true`, `|| echo 0`,
  reading `$?` through a pipe) — is **not** covered here: it needs a `.shs`
  scanner, not a `.spl` lint rule. Filed as follow-up.

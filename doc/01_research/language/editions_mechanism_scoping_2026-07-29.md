# Editions mechanism — scoping (lane ED1 `editions-scoping-plus-manifest`)

**Status:** research/scoping, no semantics gated
**Date:** 2026-07-29
**Prompted by:** mission-critical robustness campaign lane ED1. Rust ships
editions (2015/2018/2021/2024) so breaking changes can be opt-in per-crate.
Simple has no equivalent — every breaking change today is either silently
absorbed (deprecated-alias-forever) or a flag day for the whole repo. This
doc scopes whether/how an edition mechanism would work, file:line-anchored
against Simple's own history. It does **not** decide edition semantics; see
"Design-decision territory" below for what is explicitly out of scope here.

## 1. Real candidates: behavior changes that were (or are becoming) breaking

Grepped from `doc/08_tracking/bug/` and `doc/02_requirements/language/mission_critical_profile.md`.
Each row is a change that either (a) already shipped as a silently-compatible
rename, (b) is an explicit phased warn-then-deny rule, or (c) is a runtime
semantic fix that would be observably breaking if corrected.

| Candidate | Evidence | Today's handling | Why it's edition-shaped |
|---|---|---|---|
| **Profile-name rename** `lib`→`strict`, `reliable`→`robust`, `mission-critical`→`critical` | `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:28-38` (`normalize_profile_name`), `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:86-105` (`parse_lint_profile` + `_warn_deprecated_profile_alias_once`) | Old spellings **kept working forever**, warn-once per process (`config_and_model.spl:60-74`). No removal path exists or is planned. | This is the shape of a change an edition *would* let you eventually retire (drop the alias table in edition N+1) instead of "warn forever." Today there is no mechanism to ever stop accepting `lib`/`reliable`/`mission-critical`. |
| **`REQ-MC-002` const-ref-default** | `doc/02_requirements/language/mission_critical_profile.md` REQ-MC-002: "Rule `W-MC-REF-001 const_ref_default` warns in all tiers now; escalates to deny in this profile at v2 — user decision 2026-07-28" | Warn now, an explicit future "deny at v2" is already named but has no mechanism to attach to | Textbook edition candidate: a rule whose severity change is a breaking behavior change, explicitly deferred to a versioned gate ("v2") that doesn't exist as a real dimension yet — it currently can only be phased by *profile* (moderate/strict/robust/critical), not by a code's declared edition. |
| **`REQ-MC-011` bare-primitive-internal** | same file, REQ-MC-011: "warn in mission-critical profile now, deny at v2" | Same warn-then-(future)-deny shape as REQ-MC-002 | Same reasoning — two independent rules both cite an undefined "v2" as their deny trigger, which is exactly the gap an edition value would fill. |
| **`iso`/`mut` capability-prefix keywords** | `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md` — `iso`/`mut` type-prefix grammar (`TypeKind.Isolated`/`TypeKind.Atomic`, `src/compiler/10.frontend/parser_types_expr.spl:32-33`) is declared but never constructed by the real parser; `fn take(a: iso i64)` is currently a parse error | Not implemented — currently dead grammar | Once implemented, `iso`/`mut` become reserved in type-prefix position everywhere. Any existing source using `iso`/`mut` as an ordinary identifier (variable, param, or type name) in that grammatical slot would break at parse time with no opt-out. A real edition boundary is the standard way to land a new reserved word without an instant flag day. |
| **`text.to_int()` / `Option<i64>` nil-sentinel semantics** | `doc/08_tracking/bug/to_int_optional_lies_and_some_i64_payload_shift_2026-07-27.md` — `rt_string_to_int` (`src/runtime/runtime_native.c:2889`) returns bare `0` on parse failure, indistinguishable from a legitimate `"0"`; `x ?? d` / `x == nil` never fire. Related family: `reference_coalesce_on_raw_i64_corrupts_index_3` (memory) — 740 `?? ` sites audited, 60% were live bugs relying on the broken sentinel | OPEN bug, not yet fixed compiler/runtime-side; call sites patched defensively | If/when the runtime is fixed to make nil actually distinguishable from `0`, any code that depended on the old fail-open behavior (`parsed ?? -999` silently returning `0` instead of `-999` for garbage input) changes observable behavior. This is exactly the class of fix Rust would gate behind an edition rather than changing everyone's programs' behavior on upgrade. |

**Pattern across all five:** Simple's current answer to "this would break someone" is
either (a) keep the old spelling alive forever (profile aliases — permanent
compatibility debt), or (b) pick a severity tier as a proxy for time
(`profile=critical` warn-vs-deny) which conflates *how strict you want to be
audited* with *which language semantics your source was written against* —
two orthogonal axes. An edition value would let (b) actually retire, and
would let a real breaking fix for row 4/5 ship without silently changing
existing programs.

## 2. Where an edition value would live

`simple.sdn` is the existing per-project manifest. Two things are true about
it simultaneously, and this is the first concrete finding of this doc:

- **The format actually on disk** (`src/compiler/simple.sdn`, `src/app/simple.sdn`,
  `src/lib/simple.sdn`, `src/compiler_rust/simple.sdn` — the only `simple.sdn`
  files that exist in this repo, none at repo root) is a nested, indentation-scoped
  tree: `project:\n  name: ...\n  version: ...\n  features:\n    default: [jit]`
  (`src/compiler/simple.sdn:3-19`). There is no `[section]`/`key=value` anywhere
  in any real `simple.sdn` in the repo (`grep -rn '\[lints\]' --include=*.sdn .`
  returns zero hits outside code comments).
- **The format the profile-resolution code expects to read** is a flat
  `[section]` header + `key = value` scanner: `_read_sdn_lints_profile`
  (`src/lib/nogc_sync_mut/test_runner/test_runner_config.spl:48-71`) and its
  twin `_run_read_sdn_lints_profile` (`src/app/io/_CliCommands/handler_commands.spl:112-136`)
  both look for a literal `"[lints]"` line, then `profile = "..."` inside it.
  This mirrors `LintConfig.from_sdn_string`'s real `[lints]` parser
  (`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:328-351`), which
  *is* real code but is never fed by any tree-format `simple.sdn` that ships
  in this repo today.

**Finding:** the profile precedent this lane is told to mirror is, as of
2026-07-29, forward-looking/dead-in-practice — no checked-in `simple.sdn`
has a `[lints]` section, so `resolve_effective_profile` always falls through
to `""` in this repo's own tree (confirmed directly by
`profile_aware_execution_spec.spl:79-84`'s own comment: "This repo's cwd
during `bin/simple test` has no simple.sdn at the root"). This is not a new
defect to fix in this lane (PE lane's scope, out of bounds per the task's
"additive edits only" instruction) — it is a fact the edition slice must
inherit rather than fight: **Phase 2 below reads a `[package]` bracket
section with the same scanner shape, for the same reason (matching the
existing profile-reader code precedent this lane was told to mirror), fully
aware that no shipped `simple.sdn` currently has one either.** If the
tree-format is ever made canonical, both the `[lints]` and the new
`[package]` readers need the same follow-up migration — tracked as an open
question in §4, not resolved here.

Where the value lives once read: a bare accessor `resolve_edition()`,
colocated with `resolve_effective_profile` in
`src/lib/nogc_sync_mut/test_runner/test_runner_config.spl` (this lane, Phase 2),
returning `text`. No `TestOptions` field, no CLI flag — nothing today asks
for an edition, so there is nothing to thread it onto yet (see §4c).

## 3. Resolution order (if/when editions gate anything)

Following the profile precedent exactly
(`test_runner_config.spl:73-81` comment: "explicit --profile= CLI flag >
simple.sdn [lints] profile= > engine default"):

1. An explicit CLI flag (e.g. a hypothetical `--edition=2026`) — **does not
   exist yet**; no CLI flag reads or sets an edition anywhere in this repo
   (`grep -rn -- '--edition' src/app` — zero hits). Not added in this lane.
2. `simple.sdn` `[package]` `edition = "2026"` — added in Phase 2 of this lane,
   parse-only.
3. Engine/compiler default — the single defined value, `"2026"`, today's
   implicit edition (every program written before this lane existed is
   retroactively "edition 2026" since there was never a prior one to name).

Tier 1 is listed for completeness/consistency with the profile precedent's
three-tier shape; it is explicitly **not implemented** by this lane (there is
nothing to resolve between CLI and manifest yet — see §4c) and should not be
read as a commitment to add a CLI flag without a design decision on whether
CLI-level edition override even makes sense (a project's edition is normally
a property of the source tree, not an invocation flag — unlike profile,
which legitimately varies per test run).

## 4. Design-decision territory (NOT resolved by this lane)

Everything below requires a human decision before more plumbing is built;
this doc surfaces the questions, it does not answer them.

**(a) What editions actually gate.** None of the five candidates in §1 are
wired to `resolve_edition()` by this lane. Deciding *which* rule reads the
edition value (e.g., "REQ-MC-002 denies under edition >= 2027" or "`iso`/`mut`
become reserved words only under edition >= 2027") is a language-design
decision with real migration cost, not plumbing. This lane adds the
accessor and stops.

**(b) Edition semantics themselves.** Rust editions bundle: reserved-word
changes, default trait bound changes, macro hygiene changes, and (crucially)
require *all* crates in a dependency graph to interoperate across editions
via a shared compiled representation. Whether Simple's editions would be
per-package (like Rust) or per-file, whether mixed-edition builds are even
supported, and what "interop across editions" means for `use std.X` imports
across `src/lib` (which currently has one implicit edition, "whatever HEAD
does") are unscoped.

**(c) Migration tooling.** Rust ships `cargo fix --edition`. Whether Simple
would need/want an automated migration tool (e.g. to rewrite `lib`/`reliable`
profile spellings, or to insert explicit primitive-type wrappers for
REQ-MC-011) is unscoped — and arguably shouldn't be designed before there is
at least one real edition-gated rule to migrate away from.

**(d) Whether `simple.sdn`'s tree format vs. the `[section]` format used by
the profile/edition readers should be unified.** This is the concrete
inconsistency found in §2. Two credible resolutions exist (make the
`[section]` readers parse the tree format instead; or migrate real
`simple.sdn` files to have literal `[package]`/`[lints]` blocks) and this
lane does not pick one — it only documents that the new `[package] edition=`
reader has the identical dead-in-this-repo status the `[lints] profile=`
reader already had, by design (matching precedent), not by oversight.

## 5. What this lane actually ships (Phase 2, decision-free plumbing only)

- `resolve_edition()` in `test_runner_config.spl`, next to `resolve_effective_profile`.
- Reads `simple.sdn` `[package]` section, `edition = "2026"` (or bare `2026`,
  quotes stripped — same normalization as the profile reader).
- Exactly one defined value, `"2026"`. Anything else: warn-once (mirroring
  `_warn_deprecated_profile_alias_once`, `config_and_model.spl:60-74`,
  module-level `Dict<text, i64>` counter keyed by the bad value, fires once
  per distinct bad value per process), fall back to `"2026"`.
- Absent `edition=` (or absent file, or absent `[package]` section): resolves
  to `"2026"` silently — that's the documented "implicit current edition,"
  not an error.
- Nothing consumes the result beyond the accessor itself and its spec. Every
  new function carries a comment: "plumbing for editions; no semantics
  gated yet — see doc/01_research/language/editions_mechanism_scoping_2026-07-29.md".

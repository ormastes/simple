# `bin/simple lint` reports "all files clean" on a module that does not parse

Date: 2026-08-09
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
see "Fresh investigation" below; not the fail-open bug it looks like)
Severity: high — lint is fail-open, so a green lint is not evidence the file compiles.
Found by: Counterpart Conformance Wave-0 lane while landing the frozen contracts.

## Fresh investigation (2026-08-09, this lane)

Re-reproduced fresh (same seed binary for both `lint` and `run`, confirmed by
banner):

```
$ bin/simple lint probe.spl   # @allow(primitive_api)\npub val X: text = "y"
Lint passed: all files clean          # EXIT=0

$ bin/simple run probe.spl
error: compile failed: parse: ... expected fn, struct, class, mixin, mod,
enum, or union after pub with attributes, found Val    # EXIT nonzero
```

Still reproduces exactly as before. But the mechanism is NOT "lint never
attempted to detect the parse failure" — that fail-open shape was fixed on
2026-07-28/08-01 (see the two referenced sibling bugs) and is proven still
working: a genuinely-broken-in-both-parsers file (`fn main(:\n    pass\n`)
correctly makes lint emit `PARSE001`/`NOT LINTED` and exit nonzero, verified
fresh in this lane.

The real cause is a **grammar divergence between two independent parser
implementations**:
- `bin/simple run`/compile uses the seed's native Rust parser
  (`src/compiler_rust/parser/src/parser_impl/items.rs`), which explicitly
  rejects any item other than `fn`/`struct`/`class`/`mixin`/`mod`/`enum`/
  `union` immediately after an outer `@attr(...)`.
- `bin/simple lint` calls `parse_module_silent_checked`, which drives the
  **self-hosted `.spl` frontend** (`src/compiler/10.frontend/core/`). Its
  outer-attribute handling
  (`_ParserDecls/enum_module_body.spl:1208-1214`, the `else:` arm for
  unrecognised annotations) is written to **intentionally** fall through and
  let the next top-level dispatch loop iteration parse whatever declaration
  follows — comment: "The following declaration is handled by the next outer
  loop iteration, which dispatches via the full elif chain (fn, use, struct,
  val, etc.)". `pub val` is accepted there with no restriction at all, so the
  self-hosted parser genuinely does not consider this file a parse failure —
  `parse_module_silent_checked` correctly returns "no error" for it, and lint
  correctly reports clean for what its own frontend can parse.

So this is not lint failing to check something it could see; it is two
grammars disagreeing about whether the input is legal, with lint honestly
reporting against the more permissive one.

## Why not fixed now

Per repo convention (CLAUDE.md), the **self-hosted `.spl` frontend is the
source of truth** ("Default tooling = pure-Simple self-hosted binary, not the
Rust seed"), and it does not restrict which items an outer attribute may
precede — this may be intentional design (the inner `#![allow(...)]` form
exists specifically for module-scoped attributes, but nothing in the self-hosted
grammar documents outer attributes as fn/struct/class/mixin/mod/enum/union-only).
Making the two parsers agree requires a decision this lane is not positioned to
make safely: either (a) tighten the self-hosted parser's outer-attribute
handling to match the Rust seed's stricter allowlist — a real but non-trivial
grammar change to shared top-level dispatch code
(`_ParserDecls/enum_module_body.spl`) that risks regressing every existing
`@attr` use across the repo without a full-corpus lint sweep first, or (b)
relax the Rust seed's native parser to match — off-limits (`src/compiler_rust/**`
is excluded from this lane's fix scope). Given `src/compiler_rust` is
bootstrap-only per CLAUDE.md, and the self-hosted grammar's current behavior
is not provably wrong (only inconsistent with the legacy seed), this is left
as a characterized grammar-divergence defect rather than patched blind.

## Symptom

`src/lib/common/spec/evidence/counterpart/model.spl` began with:

```
@allow(primitive_api)
# Counterpart Conformance — frozen Wave-0 contracts …

pub val COUNTERPART_EXTENSION_SCHEMA: text = "simple.sspec.counterpart.v1"
```

`bin/simple lint src/lib/common/spec/evidence/counterpart/model.spl` printed:

```
Lint passed: all files clean
EXIT=0
```

Loading the same file through `bin/simple run` failed immediately:

```
error: compile failed: parse: in ".../counterpart/model.spl":
Unexpected token: expected fn, struct, class, mixin, mod, enum, or union
after pub with attributes, found Val
EXIT=1
```

## Root cause of the parse error (the user-facing half)

An `@attr(...)` outer attribute binds to the next item, and `pub val` is not an
attributable item. Files that carry `@allow(primitive_api)` successfully
(`src/lib/nogc_sync_mut/engine/physics/collision2d.spl:2`,
`contact2d.spl:1`) all happen to have a `fn`/`struct` as their first item, so the
restriction was never visible.

Workaround: use the inner-attribute form `#![allow(primitive_api)]`, which is
module-scoped and does not bind to the following item. That is what the
counterpart contracts now use, and both lint (0 errors) and `run` (18 examples,
0 failures) pass with it.

## The actual defect

The parse failure is arguably correct behaviour. **Lint reporting the file clean
is not.** Lint must not emit `Lint passed: all files clean` for a file its own
front end could not parse; a parse failure has to surface as a lint error, not
as silence. As it stands, `bin/simple lint <file>` returning 0 proves nothing
about whether the file compiles, which makes it useless as the pre-commit gate
the dev workflow treats it as.

This is the same fail-open shape already recorded for other verification layers
(see `doc/08_tracking/bug/` entries on fail-open verification): the check runs,
finds nothing because it never got far enough to look, and reports success.

## Reproduction

```bash
printf '@allow(primitive_api)\npub val X: text = "y"\n' > /tmp/probe.spl
bin/simple lint /tmp/probe.spl      # expect: clean, exit 0  (WRONG)
bin/simple run  /tmp/probe.spl      # expect: parse error, exit 1
```

## Unblock condition

`bin/simple lint` treats a parse failure in a target file as a lint **error**
(non-zero exit, file named), so that a clean lint verdict implies the file at
least parses. Until then, never accept a green lint as evidence a module loads —
run the module or a spec that imports it.

## Related

- Frozen contracts: `src/lib/common/spec/evidence/counterpart/model.spl`
- Spec that caught it: `test/01_unit/infra/counterpart/contract_model_spec.spl`
- Lint rule involved: `src/compiler/35.semantics/lint/primitive_api.spl`

## Re-verified 2026-08-17 (worker s3_rust_other) — LIVE as a grammar divergence

`src/compiler_rust/parser/src/parser_impl/items.rs:681` still hard-rejects
non-`fn/struct/...` items after `pub` + attributes ("fn, struct, class, mixin,
mod, enum, or union after pub with attributes"), while the self-hosted frontend
that lint drives accepts `pub val` there. The divergence — and therefore the
clean-verdict-on-a-file-the-seed-cannot-parse symptom — is present in current
source; the PARSE001/NOT-LINTED fail-open path is intact.

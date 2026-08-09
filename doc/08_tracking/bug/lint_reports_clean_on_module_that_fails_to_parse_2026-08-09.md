# `bin/simple lint` reports "all files clean" on a module that does not parse

Date: 2026-08-09
Status: OPEN
Severity: high — lint is fail-open, so a green lint is not evidence the file compiles.
Found by: Counterpart Conformance Wave-0 lane while landing the frozen contracts.

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

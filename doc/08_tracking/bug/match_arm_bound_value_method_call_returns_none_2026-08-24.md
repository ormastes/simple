# JIT: reading through a `case Some(x)` binding answers as if every key were absent

**Date:** 2026-08-24
**Severity:** HIGH (silent wrong answers, not a crash — two hardening exit gates were dead for days because of it)
**Status:** OPEN in the JIT. Two call sites worked around; the defect itself is NOT fixed.
**Discriminator:** fails under default `bin/simple run` (JIT), passes under `SIMPLE_EXECUTION_MODE=interpreter`, and passes under `bin/simple test`.

## The defect

A value bound by a `case Some(x)` match arm is degraded under JIT: calling a
method on it answers as if the value were empty. It stays degraded when passed
on as a function argument. Assigning it to a `var` first restores it.

Measured A/B/C on one parsed SDN document, same value in all three arms:

```text
inline-arm  : av.get("waivers") inside `case Some(av)`     -> MISSING
hoisted-var : var h = av (assigned in the arm), h.get(...) -> FOUND
param       : `case Some(av): f(av)`, f does v.get(...)    -> MISSING
```

The key really is present — dumping `as_dict().keys()` on the same node lists
`enum,schema_abi,constructor` while `item.get("schema_abi")` returns None.

## Proof it is the JIT, not the language

`src/app/check/completeness_seal_census.spl` over two tracked manifests, with
the un-hoisted parser in place:

| execution mode | `PARSE-FAIL` lines |
|---|---|
| `bin/simple run` (default, JIT) | **2** |
| `SIMPLE_EXECUTION_MODE=interpreter bin/simple run` | **0** |

Same source, same fixtures, same binary. The interpreter is right.

## Why it survived: every existing spec constructs values in process

`package_pins_spec.spl` (26), `completeness_seal_spec.spl` (11),
`loader_admission_spec.spl` (11) and `source_manifest_spec.spl` (11) are all
green — 59/59 — before and after. They build manifest values directly and never
parse a real `.sdn` file, so none of them touches the affected path. A spec
written specifically to parse the tracked fixture ALSO passes pre-fix, because
`bin/simple test` uses a different evaluator than `bin/simple run`. **There is
no spec-level regression test that can catch this class** — the exit gates,
which drive `bin/simple run`, are the only thing that bites.

## Workarounds landed (product code, semantics-preserving)

- `src/compiler/00.common/assurance/package_pins.spl` — `_parse_waivers` hoists
  `assurance`, `waivers`, and the array before reading. Was returning zero
  waivers with `parse_fail=0` and no missing-field error, so E-PIN-001/002/003
  were never reached.
- `src/compiler/99.loader/completeness_seal/manifest.spl` —
  `parse_manifest_text` hoists the `extension:`/`module:` nodes before passing
  them to the sub-parsers, and `_parse_extends` hoists the sequence and each
  item's `schema_abi`. Was failing valid manifests with
  `module.extends.schema_abi missing`.

Both files already used the hoist idiom elsewhere (`var project = root` +
`case Some(pv): project = pv`), which is why `_parse_deps` was never affected —
the fix makes the file internally consistent rather than introducing a new
pattern.

## Evidence

| gate | pre-fix | post-fix |
|---|---|---|
| `check-critical-package-pins.shs` | `ERROR — nothing was checked (selftest failed: waiver-no-owner-not-detected waiver-no-expiry-not-detected waiver-expired-not-detected)` | `PASS — 1 pinned package(s) checked, advisory-in-critical=0 waiver-without-expiry=0` |
| `check-completeness-seal.shs` | `ERROR — nothing was checked (selftest failed: positive-fixture-not-admitted positive-fixture-not-published open-dyn-in-critical-not-detected id-collision-not-detected)` | `PASS — 2 selected constructor(s) checked, missing-capabilities=0 id-collisions=0 dyn-in-critical=0` |

Each fix was reverted individually and the corresponding gate went back to
ERROR, then restored to PASS — all three observations made.

## Resume — the actual fix

- **Owner:** JIT / seed codegen lane.
- **Repro:** revert either hoist above and run the census under default `run`,
  then under `SIMPLE_EXECUTION_MODE=interpreter`; the two disagree.
- **Scope risk:** this is a silent-wrong-answer class, not a crash. Every
  `case Some(x)` arm in the tree that reads through the binding under `run` is
  suspect. No census of such sites has been done.
- **Done when:** the un-hoisted parser gives identical results under JIT and
  interpreter, with a fixture that fails pre-fix under `run`.

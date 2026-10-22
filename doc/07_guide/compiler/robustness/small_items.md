# Robustness small items

Small detection features from the 2026-10 robustness priority cut. Each has
one acceptance spec under `test/01_unit/compiler/robustness/`. None of them
runs inside a compiler build, so none changes bootstrap time.

| Item | Prevents | Reports as | Off / level switch |
|---|---|---|---|
| 5a | a module static typed differently depending on visit order | spec failure | none (test only) |
| 18 | a slice materialised per loop step (perf cliff) | lint `PERF-SCAN-002` (warning) | lint name `linear_scan_in_loop`; `SIMPLE_LINT_LINEAR_SCAN` |

## 5a — static typing is order-independent

`small_items_5a_static_typing_order_acceptance_spec.spl` lowers one set of
module-level declarations in five source orders and two name orders and
compares the owner's MIR static storage, the HIR ABI interface digest
(`hir_abi_interface_digest_v1`) and an importer's storage with the provider's
constants visited forwards and backwards.

Names matter more than line order: `module.constants.values()` is not in
source order, so the spec also renames the derived statics to sort before
(`aa_`) and after (`zz_`) their operands.

To add a case, append a declaration to `SETTLED` (type settled at the
declaration) or `DERIVED` (type recovered from operands) and its name to the
matching `*_NAMES` list.

Known limits: an importer refuses an unannotated derived static
(`pub val passed = executed - failed`) with "lacks a resolved storage type;
annotate the declaration", and the ABI digest refuses it as unresolved
inference. Both refusals are the same in every order, which is all this item
checks. Owner and importer also describe an aggregate's storage differently;
that is a cross-module identity question, not an ordering one.

## 18 — PERF-SCAN-002, slice compared per loop iteration

`PERF-SCAN-001` (whole-container scan in a loop) already existed. This adds
the shape behind the 890 s SCV cold init:

```simple:skip
while i <= slen - sublen:
    if s[i:i + sublen] == sub:    # PERF-SCAN-002: one substring per step
        return i
    i = i + 1
```

It fires on `recv[a:b] == x`, `x == recv[a:b]` and `!=`, in a loop body or a
`while` condition, when at least one bound is not a literal. Use
`.index_of(sub, start)` or `.starts_with` instead.

It does not fire:
- outside a loop, or on a slice that is kept rather than compared;
- inside a `"` or `'` literal, or after a `#` comment;
- on a one-wide slice compared with a one-character literal
  (`s[i:i + 1] == "*"`). That is a single-byte test, not a scan. No
  replacement idiom is suggested for it: its native cost was not measured.

Level: lint name `linear_scan_in_loop` in `simple.sdn` (`allow`, `warn`,
`deny`; default `warn`). `SIMPLE_LINT_LINEAR_SCAN=off` skips the scan;
`error` reports at deny; anything else warns.

To add a shape, extend `slice_compared_for_equality` in
`src/compiler/35.semantics/lint/linear_scan_in_loop.spl` and add a fixture to
the spec.

Known limits: line-based, so a comparison split over two lines is missed. On
the seed interpreter the static rule table returns no findings for any
imported rule, and `seed lint` crashes on Windows, so the rule is verified
through its public entry, not through the CLI.

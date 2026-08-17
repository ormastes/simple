# Private module helper `_has` silently resolves to the wrong function across modules

- Date: 2026-08-17
- Severity: high (silent wrong answers, not a crash)
- Engine: tree-walk interpreter (`bin/simple test`); binary
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`test/01_unit/app/build/build_targets_spec.spl` reported **45 total, 38 passed,
7 failed**, every failure `expected false to equal true`. All 7 were assertions
routed through the spec-local helper:

```
fn _has(errors: [text], needle: text) -> bool:
    var i = 0
    while i < errors.len():
        if errors[i].contains(needle):
            return true
        i = i + 1
    false
```

## Diagnosis — the implementation is correct

Reduced in a scratch spec with the same import set. Within one `it` block:

| assertion | verdict |
|---|---|
| `expect(errs.len()).to_equal(1)` | PASS |
| `expect(errs[0]).to_equal("target-error: duplicate-name: a")` | PASS |
| inline `while` loop with `errs[i].contains(...)` | PASS |
| `expect(errs[0].contains("duplicate-name: a"))` | PASS |
| `expect(_has(errs, "duplicate-name: a"))` | **FAIL** |
| `_has` on a *literal* `[text]` holding the same string | **FAIL** |

So `validate_targets` in `src/app/build/targets/build_targets.spl` produces the
exact expected error strings; only the call through `_has` returns `false`.

## Trigger is the import set, not the helper body

The identical helper and assertions PASS in a spec that imports only
`build_targets` + `std.io_runtime` + `app.io.mod`. They FAIL once the spec also
imports `target_resolve`, `targets_cli`, `target_executor`, `bootstrap_policy`,
`build_explain` — i.e. once the transitive module set grows.

Renaming the helper `_has` -> `_errors_contain`, changing nothing else, turns
the reduced spec from 2 failures to **6/6 green**, and the real spec from
38/45 to 45/45.

This is the same failure mode as the interpreter's own warning
`compiler_cross_module_private_symbol_collision`: private module-level symbols
are resolved by NAME across modules, so a leading-underscore "private" helper
is not private. Near-miss names present in the tree include `_has_token`,
`_has_edge`, `_has_extension`, `_has_any_agg`, `_hash_key`. Unlike the class
case, no warning was emitted for this function collision.

## Unblock condition

Make module-private (`_`-prefixed, non-`pub`) top-level functions resolve
module-locally in the interpreter, or at minimum emit the
`cross_module_private_symbol_collision` diagnostic for functions as it already
does for classes. Until then, spec-local helpers need globally unique names.

## Workaround applied

`test/01_unit/app/build/build_targets_spec.spl`: `_has` -> `_errors_contain`.
No assertion was weakened; no product code changed.

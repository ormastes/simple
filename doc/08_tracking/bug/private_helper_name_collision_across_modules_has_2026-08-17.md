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

## Re-verification 2026-08-17 (app-rest lane) — LIVE by content; specs added

Static confirmation (content, not SHA ancestry): the colliding definition is
still present at `src/app/build/targets/change_classifier.spl:56`

    fn _has(values: [text], value: text) -> bool:   # EQUALITY semantics

and the workaround is still load-bearing in the spec — the helper there is now
named `_has_error`, with an explanatory comment at
`test/01_unit/app/build/build_targets_spec.spl:32-37`. (Note the drift: this doc
records the rename as `_errors_contain`; the tree uses `_has_error`.) Nothing in
the interpreter makes `_`-prefixed top-level functions module-local, and no
`cross_module_private_symbol_collision` diagnostic is emitted for functions.
Verdict: LIVE.

Two specs were added for this record:
- reproducing: `test/01_unit/app/build/private_helper_name_collision_spec.spl`
  — declares a spec-local `_has` with SUBSTRING semantics under the same import
  closure and asserts it keeps its own body.
- class-detection: `test/01_unit/app/build/private_helper_collision_class_spec.spl`
  with fixtures `test/fixtures/compiler/private_collision_mod_a.spl` and
  `private_collision_mod_b.spl` — two modules sharing the private helper name
  `_collision_probe_shared` with different bodies (+1 vs +100), asserting each
  pub wrapper resolves to its OWN module. This generalises past the `_has`
  instance, so a future recurrence under any other name is still caught.

NOT YET VERIFIED BY EXECUTION. Both spec runs were killed under concurrent
bootstrap load (host load average 60-106) and produced **no `Results:` line**:
the class spec returned `rc=143` (SIGTERM) after the full module-loading dump,
and the wrapper still reported `[exited with code 0]` — exactly the false-green
laundering the lane brief warns about. Per lane convention an absent `Results:`
line is UNVERIFIED, never a pass or a fail. Both specs need a re-run on a quiet
host before this record is closed or its severity changed.

The fix itself is out of this lane's file scope: it belongs in the interpreter's
free-function resolution (make `_`-prefixed non-`pub` top-level functions
module-local), or at minimum extend the existing
`cross_module_private_symbol_collision` diagnostic from classes to functions.

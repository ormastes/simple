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

### Correction to the paragraph above — BOTH spec runs ended rc=143

The note above described only the class spec as SIGTERMed. The reproducing spec
has since finished the same way. Final state of both attempts:

    private_helper_collision_class_spec.spl      -> Terminated, rc=143
    private_helper_name_collision_spec.spl       -> Terminated, rc=143
      (re-run with --timeout 1500, host load average 60-106)

Neither produced a `Results:` line; both logs stop inside the module-loading
warning dump (90,554 bytes, byte-identical between the two runs, i.e. neither
reached its first example). Both wrapper invocations still reported
`[exited with code 0]`.

`rc=143` is SIGTERM from outside the process, not a spec failure and not a
timeout of the spec runner itself — a `kill_simple_monitor` instance is
terminating long-running `simple` processes on this host. So these two runs
carry ZERO evidence about the defect in either direction. The specs remain
UNVERIFIED and must be re-run on a quiet host, ideally with the monitor
stopped or its MIN_AGE_SECS raised above a normal spec runtime.

## Re-run 2026-08-17 on a quieter host — BOTH SPECS NOW HAVE A `Results:` LINE

The two runs above ended `rc=143` with no verdict and were therefore worthless.
They have now been re-run to completion.

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
**59537240 bytes, mtime 2026-08-17 12:58:51** (Rust seed).

```
$ timeout 3000 nice -n 19 bin/simple test test/01_unit/app/build/private_helper_collision_class_spec.spl
rc=0
Results: 4 total, 4 passed, 0 failed

$ timeout 3000 nice -n 19 bin/simple test test/01_unit/app/build/private_helper_name_collision_spec.spl
rc=1
Results: 3 total, 0 passed, 3 failed      (Duration: 65576ms)
```

`rc` was assigned on the line after each command, never read through a pipe.

**Verdict: the defect is LIVE and now proven by EXECUTION, not only by content.**
The reproducing spec — a spec-local `fn _has(errors: [text], needle: text) -> bool`
with SUBSTRING semantics, under the `app.build` import closure that also loads
`src/app/build/targets/change_classifier.spl:56`'s `fn _has(values: [text], value: text) -> bool`
with EQUALITY semantics — fails **all three** of its examples. The spec-local
body does not survive; the other module's wins.

### New finding: the two specs disagree, and that is the informative part

The class-detection spec passes 4/4. It uses two purpose-built fixtures
(`test/fixtures/compiler/private_collision_mod_{a,b}.spl`) that share the private
name `_collision_probe_shared`, and each pub wrapper correctly reaches its OWN
module's body. So a two-fixture-module pair is NOT sufficient to trigger this —
consistent with the original filing's observation that the trigger is the SIZE of
the import closure, not the presence of a duplicate name. The generalisation spec
is therefore currently a passing control, not a reproducer; it must not be read
as evidence that the defect is fixed. Only
`private_helper_name_collision_spec.spl` reproduces.

### Why no diagnostic fires (answers the record's "at minimum" ask)

The "at minimum emit the diagnostic for functions" unblock condition is
**already implemented and still does not help here.**
`src/compiler_rust/compiler/src/pipeline/module_loader.rs`
`warn_duplicate_private_signatures` (`:1552`) explicitly refuses to skip
`_`-prefixed names — there is a comment at `:1570-1574` forbidding a
`starts_with('_')` skip — and it classifies such a name as `"private helper"`
(`:1607-1613`). But the two `_has` definitions have the **same** signature
`([text],text)->bool`, so the collision falls into the SAME-SIGNATURE arm at
`:1615+`, which is gated behind `same_signature_diag_enabled()` (`:1537-1550`):

> Default OFF. ... Opt in with `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`.

Re-running the reproducing spec with that gate open still printed no
`private helper \`_has\`` line:

```
$ SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 timeout 3000 nice -n 19 \
    bin/simple test test/01_unit/app/build/private_helper_name_collision_spec.spl \
    2>&1 | grep -E 'private helper `_has`|Results:'
Results: 3 total, 0 passed, 3 failed
```

So the warning does not fire **even with the env gate open**, which means the
two definitions are not both present in `module.items` by the time
`warn_duplicate_private_signatures` runs — one has already been dropped by the
flatten pass. That is a stronger statement than the original filing's "no warning
was emitted": the diagnostic is not merely off, it is structurally unable to see
this case. Any real fix must act at flatten/registration time, not at the
warning.

### Status

**OPEN**, severity unchanged (high, silent wrong answers). Now backed by an
executed `Results:` line rather than by content inspection. The workaround
(`_has_error` in `build_targets_spec.spl`) remains load-bearing and must not be
reverted. Not fixed here: the mechanism is in the Rust seed's module flatten /
free-function registration, not in pure-Simple source.

## Re-run 2026-08-17 on the NEWLY REDEPLOYED Rust seed — STILL RED

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

```
$ timeout 3000 nice -n 19 bin/simple test \
    test/01_unit/app/build/private_helper_name_collision_spec.spl --no-session-daemon
  ✗ resolves a spec-local private `_has` to the spec's own substring body
  ✗ does not degrade the local substring helper into equality
  ✗ still routes real validate_targets errors through the local helper
Results: 3 total, 0 passed, 3 failed
EXIT=1

$ timeout 3000 nice -n 19 bin/simple test \
    test/01_unit/app/build/private_helper_collision_class_spec.spl --no-session-daemon
Results: 4 total, 4 passed, 0 failed
EXIT=0
```

**Verdict: STILL-OPEN.** Counts identical to the previous pass (3/3 fail, 4/4
control pass); the seed rebuild carried no change to the module flatten /
free-function registration path.

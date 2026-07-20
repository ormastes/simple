# Match arm: bare identifier resolving to a module `val` lowers as an irrefutable binding

**Bug ID:** `match_bare_ident_const_irrefutable` (see `doc/08_tracking/bug/bug_db.sdn`)
**Status:** OPEN — worked around in `src/app/devhub/errors.spl`
**Severity:** P2 (silent-wrong result, no diagnostic)

## Symptom

A `match` statement over a plain scalar (`text`/`i64`/...) subject whose arm
patterns are bare identifiers that happen to resolve to an existing top-level
`val` constant does NOT compare the subject against the constant's value.
Instead the interpreter lowers the bare identifier as an irrefutable
capture-binding pattern — the arm always matches, regardless of the subject's
actual value. Only the FIRST such arm's body ever runs; later arms
(including the same-shaped bare-identifier arms and any trailing `_`) are
unreachable, and no unreachable-pattern diagnostic is emitted.

This is distinct from
`doc/08_tracking/bug/native_const_pattern_lowers_irrefutably_2026-07-13.md`,
which requires an enum-variant name colliding with an unrelated struct name.
This bug reproduces on a plain `text` subject with module-level `val text`
constants and NO enum, NO struct, and NO name collision at all.

## Minimal repro (bootstrap seed, `bin/simple run`)

```simple
val FOO = "foo_tag"
val BAR = "bar_tag"

fn classify(k: text) -> i64:
    match k:
        FOO: 100
        BAR: 200
        _: 999

fn classify_lit(k: text) -> i64:
    match k:
        "foo_tag": 100
        "bar_tag": 200
        _: 999

fn main():
    print("const-match BAR -> {classify(BAR)}")        # got 100, want 200
    print("const-match FOO -> {classify(FOO)}")         # got 100 (correct by luck)
    print("const-match unknown -> {classify(\"zzz\")}") # got 100, want 999
    print("lit-match BAR -> {classify_lit(BAR)}")        # 200 (correct)
    print("lit-match FOO -> {classify_lit(FOO)}")        # 100 (correct)
    print("lit-match unknown -> {classify_lit(\"zzz\")}") # 999 (correct)
```

Output:
```
const-match BAR -> 100
const-match FOO -> 100
const-match unknown -> 100
lit-match BAR -> 200
lit-match FOO -> 100
lit-match unknown -> 999
```

Every `const-match` call returns `100` — the value of the first arm — proving
the match is irrefutable once a bare-identifier pattern appears. Replacing
the bare identifiers with equivalent string literals (`lit-match`) produces
the correct, expected result.

## Real-world instance found

`src/app/devhub/errors.spl` `ItfError.exit_code()` used:

```simple
match self.kind:
    ITF_ERR_AUTH: 4
    ITF_ERR_CANCELLED: 2
    _: 1
```

`ITF_ERR_AUTH` is a top-level `val text` constant (`"auth_required"`). Because
of this bug, `exit_code()` returned `4` for every `ItfError` regardless of
`kind` — `cancelled`/`api_error`/`not_found`/`version_conflict` all got the
`auth_required` exit code. This produced 4 long-standing test failures in
`test/01_unit/app/devhub/itf_config_spec.spl` (recorded in
`doc/08_tracking/test/test_result.md` since 2026-05-19).

## Workaround applied

Rewrote `exit_code()` as an `if`/`else if`/`else` chain using `==` on `text`
(a code path already proven correct elsewhere in the same file, e.g.
`display()`'s `if trace_id != "":`), instead of `match`:

```simple
if kind == ITF_ERR_AUTH:
    4
else if kind == ITF_ERR_CANCELLED:
    2
else:
    1
```

This keeps the `ITF_ERR_*` constants as the single source of truth (no
duplicated literal strings) while avoiding the match landmine entirely.

## Required fix

Match-arm lowering must resolve a bare identifier pattern against the current
scope BEFORE deciding it is a fresh capture binding: if the identifier
resolves to an existing module-level `val`/`const` (of a type compatible with
the match subject), lower it as a value-equality pattern against that
constant, matching how Rust distinguishes path/const patterns from binding
patterns during name resolution. This should apply uniformly for scalar
subjects (this bug) and enum subjects with same-named unrelated structs
(2026-07-13 bug), since both stem from the same missing resolve-before-bind
step in pattern lowering.

## Impact

Any `match` over a `text`/scalar field compared against named `val`
constants (a common pattern for "typed string enum" modules, e.g. the
`ITF_ERR_*` tag constants used throughout `src/app/devhub/`) is at risk of
this silent-wrong behavior with zero compiler diagnostic. Recommend an
`unreachable pattern` lint as a cheaper interim mitigation even before the
resolve-before-bind fix lands.

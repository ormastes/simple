# A `new` identifier after a named-argument `:` still raises the bogus "Common mistake" ERROR

- Status: OPEN (2026-09-13, found during UNIT-P1 continuation)
- Binary: `/home/yoon/cargo-unitp1/release/simple`, sha256 `d4c0779cef6cf0cc4054` (this lane's own rebuild, already carries the fix from `932ab196848`)
- Base: `work/unit-p1-2026-09-13` at `5eef5b0c1b0`
- Area: `src/compiler_rust/parser/src/error_recovery.rs:414-455` (`detect_common_mistake`)
- Related, already fixed: `doc/08_tracking/bug/java_new_hint_fires_after_comparison_operators_2026-09-13.md`

## Found via

Bisecting the one residual `Common mistake detected: Use struct literal: Type
{ field: value }` hit in the `test/01_unit/os` rerun on the fixed binary
(`932ab196848` deployed), in `test/01_unit/os/services/nvfs/posix_shim_test.spl`
-> `src/os/services/nvfs/posix/fs_driver_impl.spl:365`:

```
self.names.push(NameEntry(path: new.raw, arena_id: arena_id))
```

`new` here is a parameter of the enclosing `fn rename(old: Path, new: Path)`
(line 346), used as the value of the NAMED ARGUMENT `path:` in a struct-style
call. The token immediately before `new` is `Colon` — not covered by the
comparison-operator fix, and not obviously coverable the same way.

## Minimal repro

```
struct NameEntry:
    path: text
    arena_id: i64

fn main():
    val new = "hello"
    val e = NameEntry(path: new, arena_id: 1)
    print e.path
```

Fires: `error: Common mistake detected: Use struct literal: Type { field: value }`.

## Why this is NOT a safe one-line allow-list add, unlike the comparison-operator fix

A colon also opens single-line block bodies, and `new Type()` immediately
after a colon in THAT position is a genuine positive case that must keep
firing:

```
fn make() -> Foo:
    if true: new Foo() else: new Foo()
```

Both fire today (correctly) — `Common mistake detected` x2 — and must
continue to. The token immediately preceding the `:` is an `Identifier` in
BOTH shapes (`path: new` — `path` is an identifier; `if flag: new Foo()` —
`flag` is an identifier too), so a single-token lookback from the `:` cannot
tell "named-argument colon inside a call's parens" from "block-opening colon
after an if/while/fn header" — they are lexically identical in the 1-token
window `detect_common_mistake(current, previous, next)` uses
(`error_recovery.rs:328`, exactly three tokens, no bracket-depth or
parse-state context).

Disambiguating correctly needs paren/bracket-depth tracking (are we inside an
unclosed `(` that started a call, vs. at statement level) threaded into this
function, which is architecturally a bigger change than the six-token
allow-list addition in the comparison-operator fix — risks a new false
negative (silently un-flagging a real `if cond: new Foo()` misuse) if done
carelessly. Per the project's own bar (fix if a safe ≤40-line change with a
test, else record), this is recorded rather than attempted here.

## Impact, measured

One confirmed spec (`posix_shim_test.spl`) affected via this path, discovered
by exhaustive elimination against a directory sweep that dropped from 87 to 1
`Common mistake` hits after the comparison-operator fix — this is the entirety
of what's left of that bucket in `test/01_unit/os`, not a new large bucket.
That one spec file also fails independently on `spipe_empty_examples`
(`lint: error: SPipe example has no real assertion or sanctioned skip`) and an
unrelated `Undefined("undefined identifier: gf128_mul")` in a sibling module
reached transitively — so fixing only this issue would not turn that spec
GREEN by itself.

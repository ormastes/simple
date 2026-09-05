# Rust-seed `JavaNew` common-mistake heuristic false-positives on a legitimate identifier named `new`

- **Filed:** 2026-08-10
- **Severity:** MEDIUM (blocks otherwise-valid source; the seed is the only
  working `bin/simple` tonight per the Stage-3 self-host blocker, so this is
  live, not theoretical)
- **Status:** OPEN — reproduced, root-caused, **not fixed** (fix would require
  editing `src/compiler_rust/**`, which is out of scope per this repo's
  standing "fix `.spl`, not Rust" rule; the seed is bootstrap-only and this
  heuristic has no equivalent implementation in the pure-Simple frontend to
  patch instead — see "Where it lives" below)
- **Area:** `src/compiler_rust/parser/src/error_recovery.rs`

## What was wrong

`new` is a real, legitimate identifier in this codebase today — e.g. function
parameters (`fn rename(old: Path, new: Path)` in
`src/lib/nogc_async_mut/fs_driver/{fat32_stub,ramfs}.spl` and
`src/lib/nogc_async_mut/fs_driver/ops.spl`; `fn compare_lockfiles(old, new)` in
`src/lib/*/package/lockfile.spl`; `fn str_replace(s, old, new)` in
`src/lib/nogc_sync_mut/src/text_utils.spl`) and local bindings (`val new =
PackageManifest.from_file(...)` in `src/lib/*/package/upgrade.spl`, 3 copies).

The Rust seed's speculative error-recovery pass
(`error_recovery.rs::detect_common_mistake`, around line 385) flags any
`TokenKind::New` token as the `JavaNew` mistake ("Use struct literal: Type {
field: value }") unless the *immediately preceding* token is one of a fixed
allow-list (`Dot`, `Fn`, `DoubleColon`, `Comma`, `LParen`, `Val`, `Var`, `Or`,
`And`, `Assign`, `Plus`, `Minus`, `Star`, `Slash`). A bare `new` used as a
**statement or return-position expression** — e.g. the last line of a function
body that simply returns the parameter — has no preceding token in that list
(the previous token is a `Newline`/`Indent`), so it is misdiagnosed as the
Java `new Type()` mistake and the parse aborts.

## Measured (Rust seed, `bin/simple run`, 2026-08-10)

Repro file:
```
fn rename(old: text, new: text) -> text:
    new

fn main():
    val new = "hello"
    print(new)
```

Output:
```
error: Common mistake detected: Use struct literal: Type { field: value }
  --> .../kwtest.spl:2:5
   |
  2 |     new
   |     ^
Use struct literal syntax instead of 'new'.
```
(`val new = "hello"` and `print(new)` both parse fine — only the bare
return-position `new` on line 2 trips the heuristic.)

## Root cause

`error_recovery.rs`'s allow-list is an incomplete enumeration of "tokens that
can legally precede an identifier". It omits `Newline`/`Indent`/`Colon`
(statement start / block start), `Return`, and `RArrow` (return-position),
among others — so any of those contexts still trip the false positive even
though `new` there is unambiguously a plain identifier reference, not a
constructor call (a real `new Type(...)` mistake is always followed by an
identifier + `(`, which this check doesn't even look at).

## Where it lives / why this isn't fixed here

- `grep -rn "Common mistake detected\|JavaNew" src/compiler/` — **zero
  matches**. The pure-Simple frontend (`src/compiler/10.frontend/parser/recovery.spl`)
  has its own `detect_common_mistake`, but it has no `New`/Java-`new` case at
  all, and (separately) that whole function currently has **no callers**
  anywhere in `src/compiler/` — it is dead code, not wired into the real
  parser dispatch. So there is no reachable `.spl` code path exhibiting this
  bug to patch, and the actual bug (in `error_recovery.rs`) is Rust seed code,
  which this repo's rules say not to touch ("fix `.spl` not Rust";
  `.claude/rules/bootstrap.md`: the Rust seed is bootstrap-only).
- This is currently *live* rather than purely theoretical because
  `bin/simple --version` reports the Rust-seed warning banner right now (see
  `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
  — Stage-3 self-host is still blocked), so the seed is the binary actually in
  use for `bin/simple run`/`bin/simple test` tonight.

## Suggested fix (for whoever next touches the Rust seed, or wires
`detect_common_mistake` into the pure-Simple parser)

Either (a) extend the allow-list with `Newline`, `Indent`, `Colon`, `Return`,
`RArrow`, `Bang` (start-of-statement/expression contexts), or (b) require a
positive signal instead of a negative one: only flag `JavaNew` when the token
immediately *after* `new` is an identifier immediately followed by `(`
(the actual `new Type(...)` shape), mirroring how `CTypeFirst` in the `.spl`
version peeks at `next_lexeme` instead of `prev_kind`.

## Not verified

- Whether the pure-Simple self-hosted binary (once Stage-3 unblocks) would
  reproduce this — it can't be tested right now because there is no working
  deployed pure-Simple `bin/simple` in this environment (worktree has none,
  and the main-repo `bin/simple` is itself the seed per the Stage-3 blocker).
- Whether any function in the current tree actually returns a bare `new` in
  this exact position (the found real-world `new` usages are all params /
  `val` bindings / non-bare uses, so none currently trip this in practice —
  the repro above is synthetic but demonstrates the class is real and would
  break the first such usage that's ever written).

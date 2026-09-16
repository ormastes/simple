# Bug: Rust seed reserves `me` as a keyword token, rejecting it as an ordinary `val`/pattern name

**Filed:** 2026-08-28
**Component:** `src/compiler_rust/parser` (seed lexer/parser), consumer: `src/app/test_daemon/light_daemon.spl`
**Severity:** High — broke the light test daemon for every seed-only worktree, degrading
`bin/simple test` for the whole compiler suite to per-spec native-SMF+MCDC execution
(2464/2464 failures observed in an isolated stage2 worktree).

## Symptom

```
bin/simple run src/app/test_daemon/light_daemon.spl
...
error: compile failed: parse: in ".../light_daemon.spl": Unexpected token: expected pattern, found Me
```

No line/column is reported by the seed's parser error, which made this look like an
exotic/newer grammar form. It is not — it is a plain local variable name colliding
with a reserved keyword.

## Root cause

`src/compiler_rust/parser/src/token.rs:155` reserves the identifier `me` as its own
token kind:

```rust
Me,  // Mutable method (modifies self)
```

i.e. the seed's lexer always tokenizes the exact text `me` as the `Me` keyword
(intended for a mutable-self method-receiver position, analogous to `self`), never as
a plain identifier. `src/app/test_daemon/light_daemon.spl`'s `claim_lane()` function
used `me` as an ordinary local variable name (`val me = "{getpid()}"`, then compared
against it three more times). The parser only accepts `Me` in the specific
method-receiver-parameter grammar position; encountering it in `val` binding /
pattern position produces "expected pattern, found Me" with no location info.

Minimal repro:

```
fn f() -> bool:
    val me = "x"
    true
```//
```
error: compile failed: parse: ...: Unexpected token: expected pattern, found Me
```

## Fix applied (this change)

Renamed the local variable `me` -> `my_pid` in
`src/app/test_daemon/light_daemon.spl:claim_lane()` (4 occurrences: the binding and
3 uses). This is semantics-preserving — `my_pid` holds exactly the same
`"{getpid()}"` string used to claim/verify daemon-lane ownership — and keeps the
seed parsable without touching the parser. See
`$S/light_daemon_parse_fix.patch` for the diff.

## Why this is filed as a grammar gap, not just a rename

`me` is a **reserved keyword** in the seed grammar (mirroring `self`), which means
**no `.spl` source file compiled by the seed may use `me` as a plain identifier**
(variable, parameter, or field name) anywhere outside the mutable-method-receiver
position. This is a silent, sitewide restriction with no clear parser diagnostic
(no location, and "expected pattern" doesn't hint that `me` is the problem unless you
already know it's a keyword). Two follow-ups worth tracking separately:

1. The seed's error message should include the file offset (`Unexpected token: ...`
   has no line:col here, unlike most of the seed's other parse errors), and ideally
   should say "`me` is a reserved keyword (mutable self-receiver); did you mean a
   different name?" for exactly this class of collision.
2. A repo-wide grep for `\bme\b` as a non-keyword identifier (variable/param/field
   name, not in receiver position) would catch any other latent instances of this
   same trap before they cause another "daemon can't start" regression under a
   seed-only worktree.

## Verification

- `bin/simple run src/app/test_daemon/light_daemon.spl` no longer raises the parse
  error (proceeds to normal daemon startup/import warnings).
- See `$S/light_daemon_parse_REPORT.md` for the full whole-compiler-tests rerun after
  this fix.

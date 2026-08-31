# 342 `SIMPLE_JIT_STRICT` suite failures: bare-root imports (`os.`, `common.`, `lib.`, `nogc_sync_mut.`) do not resolve on the native/HIR path

Filed 2026-08-31. Status: OPEN. Class: compiler / module resolution.
Verdict: **the gate is working correctly** — it surfaced a real, large, pre-existing defect.

## Summary

A full-suite run (`SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple test --no-cover-check`,
binary built from `b0be388ec46`) produced **342 `SIMPLE_JIT_STRICT` occurrences
across 339 distinct specs**. All 342 are one class: `cannot resolve import`.
None are the tail-return, receiver-mutation, or cross-module private-symbol
collision classes fixed/known today — the `$dupN` collision text appears in the
log only as *warnings*, never among the failures.

The root cause is not the coverage lane and not the JIT. It is that the module
resolver used on the **native/HIR compile path** does not accept the bare source
roots (`os.`, `common.`, `lib.`, `nogc_sync_mut.`, `serialization.`) that the
**interpreter accepts**. The coverage/MC/DC lane is merely the only lane that
forces a spec through the native compile path, so it is the only lane that sees
it.

## Minimal reproducer (no test runner, no coverage, no wrapper)

```
$ cat zz_std.spl
use std.os.crypto.blake2b.{blake2b}
fn main():
    print("ok")
$ simple compile zz_std.spl ; echo $?
0                              # std-prefixed form: resolves

$ cat zz_bare.spl
use os.crypto.blake2b.{blake2b}
fn main():
    print("ok")
$ simple compile zz_bare.spl ; echo $?
error: cannot resolve import `os.crypto.blake2b`:
  module path segment `os` not found  [E1034]
1                              # bare-root form: does NOT resolve
```

Both name the same file, `src/os/crypto/blake2b.spl`.

Note the in-tree control: `simple compile test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl`
fails identically **at its real repo path**. This is *not* an artifact of the
wrapper being copied to `/mnt/data/tmp` — a hypothesis this investigation tested
and refuted.

## Scale

Bare-root import sites (`grep -rhoE "^use (os|common|lib|nogc_sync_mut|serialization)\."`):

| root | `test/01_unit/` | `src/` |
|---|---|---|
| `os` | 2328 | 5455 |
| `common` | 1282 | 1499 |
| `lib` | 479 | 288 |
| `nogc_sync_mut` | 71 | 242 |
| `serialization` | 5 | — |

~11,000 call sites. Every one is interpreter-only today.

## Why it surfaced now

`b0be388ec46` (PR #157) made "a coverage run whose wrapper won't compile is an
ERROR, not a pass". Before it, these degraded silently to the interpreter and
reported PASS. The suite binary was built from *exactly that tree*, so the 342
failures are the direct, intended consequence of #157 doing its job.

Separately, `exec_core.rs:1457-1465` escalates the `cannot resolve import`
class **unconditionally** — it is not gated on the env var and merely reuses the
`SIMPLE_JIT_STRICT:` prefix in its message. `SIMPLE_JIT_STRICT` was never set by
the operator. The escape hatch for this class is `SIMPLE_ALLOW_UNRESOLVED_IMPORTS=1`
(read at `hir/lower/module_lowering/module_pass.rs:43`), which must NOT be used
to silence this — it restores warn-and-continue and re-hides the defect.

## Failing specs by directory (339 distinct)

| dir | count |
|---|---|
| `test/01_unit/lib/common` | 275 |
| `test/01_unit/lib/crypto` | 24 |
| `test/01_unit/lib/nogc_sync_mut` | 14 |
| `test/01_unit/lib/hardware` | 10 |
| others | 16 |

## Where the fix belongs

`src/compiler_rust/compiler/src/module_resolver/resolution.rs`. It knows
`std`, `std_lib`, `lib`, and `src.std` (lines 498, 505, 518, 670, 733) but has
no mapping for a bare `os.`/`common.`/`nogc_sync_mut.` root onto `src/os/…` and
`src/lib/common/…`.

Deliberately **not** fixed in this change: the edit is one resolver function but
it re-points ~11,000 import sites onto a path they have never been compiled
through, so it needs its own reviewed change with a spec corpus behind it, not a
drive-by. Filing beats a rushed resolver edit.

## Not to be done

Do not weaken or disable the escalation, and do not set
`SIMPLE_ALLOW_UNRESOLVED_IMPORTS=1` in any lane. Both re-hide a real defect that
#157 was written to expose.

## Overlap

Four sibling branches work the coverage-wrapper class:
`fix/cov-wrapper-hir-lowering` (#164), `fix/cov-wrapper-optional-lteq` (#156),
`fix/cov-wrapper-rbracket-val` (#155), `fix/cov-wrapper-undefined-identifiers`
(#163). **None touches module resolution** — this class is unaddressed by all
four.

# `extern class` constructor is not callable — `SimpleError` fails with E1002

## Closed 2026-09-13 — FIXED (one line in `src/lib/common/error.spl`), verified by running

**Status: CLOSED (fixed).** Root cause isolated, fix applied, both lanes green.

### Reproduced first

The entry's own program, on the Rust seed `build/vt4/bootstrap/simple.exe`:

```
use std.error.{SimpleError, error}
val e = error("boom")
print "msg={e.message} code={e.code}"
```

failed identically on the default JIT lane **and** on
`SIMPLE_EXECUTION_MODE=interpret`:
`error[E1002]: function `SimpleError` not found`.

### Root cause isolated to the `extern` keyword alone

A/B on two otherwise byte-identical local modules — same fields, same
constructor, same `export`, differing only in the declaration keyword:

| declaration | result |
|---|---|
| `class SimpleError:` | `msg=boom code=0` — works |
| `extern class SimpleError2:` | `E1002: function `SimpleError2` not found` |

So it is not a link problem with *this* type, an import problem, or a
declaration-visibility problem: `extern class` simply does not register a
constructor. The entry's own diagnosis ("It is a LINK problem, not a missing
declaration") was on the right track.

### Why plain `class` is the correct fix here, not a workaround

The docstring claimed `SimpleError` "is a builtin runtime type". It is not —
searched and found **nothing** backing it:

- no `SimpleError` anywhere in `src/runtime/**` C sources
- no `SimpleError` in the frontend (`src/compiler/10.frontend/**`)

and every use in `src/lib/**` (`nogc_async_mut/net/sffi.spl`,
`nogc_sync_mut/net/*`, `gc_async_mut/net/*`, `play/cdp/client.spl`,
`security/enforcement/capability.spl`) only ever *constructs* it from Simple
code via `error(...)` and threads it through `Result<T, SimpleError>`. Nothing
external ever supplies an instance, so there is no foreign representation for
`extern` to be describing.

### Fix

`src/lib/common/error.spl:9` — `extern class SimpleError:` -> `class SimpleError:`.

### Verified

- The reported program now prints `msg=boom code=0` on **both** the default JIT
  lane and `SIMPLE_EXECUTION_MODE=interpret`.
- Consumer regression check: a program that imports
  `std.nogc_async_mut.net.sffi` (the module declaring
  `file_write_bytes(...) -> Result<(), SimpleError>`) alongside `std.error`,
  builds an `Err(error("x"))` and `match`es it, prints `err=x code=0`. The
  SFFI consumers still load and the `Result<(), SimpleError>` shape still
  matches.

### One correction to the report

The entry says `SimpleError` is declared twice, at `src/lib/common/error.spl:9`
and `src/lib/common/error/error.spl:15`. **The second file no longer exists.**
There is exactly one declaration today, which is also why the fix is a single
line.

### Left open elsewhere

The general defect — *`extern class` registers no constructor for any type* —
is broader than `SimpleError` and is NOT fixed by this change; the A/B above is
a clean minimal repro for whoever takes it. It was not fixed here because the
constructor-registration path is in the seed (`src/compiler_rust/**`), which was
off-limits during this pass (concurrent bootstrap).


- **Status:** open
- **Date:** 2026-08-02
- **Found at:** `f3354f1924ab032503ae64f8761c8c067e76656b`
- **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple`, which announces
  itself on startup as the **Rust bootstrap seed**. No pure-Simple binary
  exists on this host, so this is seed-path evidence and needs re-confirming
  once one does.
- **Found while:** driving down the dangling-reference backlog
  (`verification_layer_orphans_and_dangling_refs_2026-08-02.md`). This is the
  real defect hiding behind 16 reports of "`SimpleError` is declared in no src
  file". It is a LINK problem, not a missing declaration.

## Symptom

`SimpleError` is declared, twice:

    src/lib/common/error.spl:9        extern class SimpleError:
    src/lib/common/error/error.spl:15 extern class SimpleError:

and `src/lib/common/error.spl:14` constructs it:

    pub fn error(message: text) -> SimpleError:
        SimpleError(message: message, code: 0)

Calling that constructor fails:

    use std.error.{SimpleError, error}
    fn main() -> i64:
        val e = error("boom")
        print("msg={e.message} code={e.code}")
        return 0

    [jit-fallback] HIR lowering error: Unsupported feature: cannot infer field
      type while lowering main: struct 'SimpleError' field 'message'
    error[E1002]: function `SimpleError` not found
    exit 1

The `error` function itself resolves — the failure is on the `SimpleError(...)`
construction inside it.

## What is NOT the cause

**Refuted: a wrong import path.** `std.error` and `std.common.error` produce
**byte-identical** failures. Both resolve the module and the `error` function.
Repointing the import fixes nothing.

    use std.error.{SimpleError, error}         -> E1002, exit 1
    use std.common.error.{SimpleError, error}  -> E1002, exit 1

**Refuted: a missing declaration.** The class is declared in two files. The
dangling-reference guard reported it as undeclared only because its
type-declaration regex did not allow an `extern` prefix; that guard blind spot
is fixed separately and the 16 reports are gone. The runtime failure is
unaffected by that fix, which is the point: the census was measuring the wrong
thing, and the underlying defect is still here.

## Blast radius

16 import sites across `src/lib/gc_async_mut/net/` — `ffi.spl`, `http.spl`,
`sffi.spl`, `net.spl`, and seven `use std.error.*` lines in `net/__init__.spl`.
`SimpleError` is documented in `src/lib/common/error.spl` as "the standard
error type used by SFFI extern fn bindings", so the whole SFFI error-return
surface is implicated, not just the net subtree.

## Why no workaround was written

A hand-written plain `class SimpleError` shadowing the extern one would make
these call sites compile and return a value that is **not** the object the
SFFI boundary actually hands back — a silent wrong answer replacing a loud
failure. Per `.claude/rules/code-style.md` and the standing no-cover-up rule,
the loud failure stays until the constructor is genuinely linked.

## Next step for the owner

Determine whether `extern class` is meant to be constructible from Simple at
all. Two shapes are possible and the tree does not say which is intended:

1. It is constructible and the HIR lowering path for `extern class` field
   inference is missing — then fix the lowering ("cannot infer field type" is
   the direct hint).
2. It is not constructible by design, and `error()` in
   `src/lib/common/error.spl` is itself the bug — then that function needs a
   real construction path and the 16 consumers need re-pointing at it.

Do not close by deleting the imports: all 16 are live uses.

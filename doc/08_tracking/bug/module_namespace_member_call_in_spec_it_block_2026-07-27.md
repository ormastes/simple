# Module-namespace member call fails inside an sspec `it` block

**Date:** 2026-07-27
**Lane:** FSDICT
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Severity:** high — silently reds whole spec files and is easy to misread as "the module didn't resolve"

## Re-verification (2026-08-10)

Reproduced fresh with the exact repro pattern (module-namespace `fs.exists(P)`
called inside an `it` block via `print "{...}"` interpolation), run through
`bin/simple test <spec>`:

```
semantic: function expects 1 argument(s), but 2 were provided
2 examples, 1 failure
spec failure: 1 of 2 example(s) failed (exit 1)
```

Identical to the originally documented symptom — the `it`-block closure still
injects an implicit `self` when calling `X.member(arg)` on a `use std.X`
module-namespace dict, for members not independently present as a bare global
name. No commit since 2026-07-27 touches this path (`git log` on this doc
shows only doc/chore syncs, no code fix). Left OPEN; this is a genuine
interpreter/HIR defect in the flat-registry / implicit-self family, not
something safely root-caused and fixed within this session's scope.

## Summary

`use std.X` binds `X` to a module-namespace **dict**. Calling a member of that
dict (`X.member(arg)`) works in ordinary code, but inside an sspec `it` block it
fails for members that are *not also present as a bare global name*, with:

```
semantic: function expects 1 argument(s), but 2 were provided
```

The receiver is being injected as an implicit `self`, so a 1-parameter function
is invoked with 2 arguments. The lookup only succeeds when the same bare name is
independently reachable in the flat global function registry (e.g. `file_exists`,
`read_file`, `is_file` — all re-exported from `std.io_runtime`), which is why the
defect looks name-dependent rather than structural.

This is another member of the documented flat-registry / bare-name hijack family
(see `interp env_get name-collision`, `interp struct name collision`).

## Minimal repro

`build/fsdict_probe/pb_spec.spl`:

```
use std.fs
use std.spec
val P = "build/fsdict_probe/pb_spec.spl"
describe "it-context":
    it "print old member":
        print "old={fs.file_exists(P)}"      # PASSES  (file_exists is also a bare global)
        expect(true).to_equal(true)
    it "print new member":
        print "new={fs.exists(P)}"           # FAILS   (exists exists only inside std.fs)
        expect(true).to_equal(true)
```

Result: `2 examples, 1 failure`, the second reporting
`semantic: function expects 1 argument(s), but 2 were provided`.

The identical expression in a plain `fn main()` prints `true`:

```
use std.fs
fn main():
    print "ex={fs.exists("build/fsdict_probe/pa.spl")}"   # -> ex=true
```

## Position sensitivity (inside `it`)

| Form | Verdict |
|------|---------|
| `val v = fs.exists(P)` then `expect(v)` | PASS |
| `expect(fs.exists(P))` with no matcher | PASS |
| `expect(fs.exists(P)).to_equal(true)` | FAIL |
| `print "{fs.exists(P)}"` | FAIL |
| `fs.exists(P) == true` inside `expect(...)` | FAIL |
| a spec-local `fn wrapper(p) = fs.exists(p)`, called from `it` | PASS |

So: assignment position is fine; interpolation / method-chain / argument position
inside the `it` closure is not.

## Engines

Reproduces identically on `bin/simple run` (JIT falls back to interpreter with
`HIR lowering error: Unknown variable: fs`) and on
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`. Binary used: repo `bin/simple`,
which prints the Rust bootstrap-seed banner.

Secondary symptom: JIT cannot lower module-namespace access at all —
`use std.fs` + `fs.<member>` always forces the interpreter fallback.

## Workarounds available today

1. Bind to a `val` first inside the `it`, then assert on the `val`.
2. Call a member whose bare name is also globally registered (`fs.file_exists`,
   `fs.read_file`).
3. Wrap the call in a module-level helper `fn` in the spec file and call that.

Workaround 2 is what the LLVM/rust/disk-boot port specs now use.

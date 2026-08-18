# `xs.first() ?? d` returns `d` when the real element is 3 — JIT only

- **Filed:** 2026-08-17
- **Status:** OPEN, live on the deployed binary. Silently wrong result, no diagnostic.
- **Severity:** HIGH (silent wrong answer, single specific value, easy to miss)
- **Class:** raw unboxed machine word handed to a runtime nil test.
  Same class as `tag_boxing_value_corruption_family_triage_2026-08-01.md` #2 —
  the residual half that the static fix deliberately does not cover.

## Repro (deployed `bin/simple`, seed, 2026-08-16)

```
fn main():
    var a: [i64] = [5, 9]
    print "first5={a.first() ?? -1}"
    var b: [i64] = [3, 9]
    print "first3={b.first() ?? -1}"
    print "get3={b.get(0) ?? -1}"
    var c: [i64] = [0, 9]
    print "first0={c.first() ?? -1}"
```

| lane | first5 | first3 | get3 | first0 |
|------|--------|--------|------|--------|
| `SIMPLE_EXECUTION_MODE=interpreter` | 5 | **3** | **3** | 0 |
| `SIMPLE_EXECUTION_MODE=jit` (default engine) | 5 | **-1** | **-1** | 0 |

Only the value 3 is affected; 5, 9 and 0 are all correct. `.max()` on `[3, 9]`
returns 9 correctly — the value, not the accessor, is what selects the fault.

## Mechanism

`TAG_SPECIAL = 0b011` (`src/compiler_rust/runtime/src/value/tags.rs:7`) and
`rt_is_none` (`src/compiler_rust/runtime/src/value/objects.rs`) call a bare word
of 3 nil. `lower_coalesce`
(`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1774`) fixed the
reported case by lowering `??` to the identity for statically non-nullable
scalars — but at lines 1815-1822 it deliberately EXEMPTS the genuinely-optional
accessors:

```rust
"first" | "last" | "get" | "min" | "max" | "pop" | "remove" | "at"
```

Those keep the runtime nil check, which is correct for absence (`[].first() ??
-1` correctly gives -1, verified) and wrong for presence-of-3: under the JIT the
payload reaches `rt_is_none` unboxed, so a present 3 reads as absent. The
interpreter holds a typed `Value` and never reaches that comparison.

The exemption comment already names this: the accessors need an Optional TypeId
to be represented honestly. Root fix is the existing plan
`doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md` — the accessor
result must be a distinguishable `T?` whose payload is BOXED across the JIT call
boundary, so absence is a tag rather than a value collision. Suppressing the nil
check for these accessors instead would trade this bug for the strictly worse
one the comment records (`[].first() ?? -1` leaking the raw sentinel 3).

## Why this was not caught before

The reported defect was `index_of` on text, and the static fix closed exactly
that shape. The detection spec written for the CLASS — sweeping every low-3-bit
value across both the plain-scalar and the optional-accessor path — is what
surfaced the residual; the reproducing shape alone stays green.

## Gates

- `test/01_unit/compiler/codegen/probe_coalesce_sentinel_collision_jit.spl` —
  run-path probe, absolute-literal oracles, one verdict line.
  JIT: `COALESCE_SENTINEL PROBE: 1 FAILURES` / `FAIL present_first_is_3 got=-1 want=3`.
  Interpreter: `COALESCE_SENTINEL PROBE: ALL PASS`.
- `test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl` —
  subprocess engine-differential spec. Currently RED **by design**:
  `Results: 3 total, 1 passed, 2 failed` (the interpreter arm passes; the JIT arm
  and the no-FAIL arm fail). Leave it red until the plan above lands.

## Standing workaround

Do not write `xs.first() ?? d` / `xs.get(i) ?? d` on integer collections.
Test emptiness explicitly (`if xs.len() > 0`) and index directly.

## Re-verified 2026-08-17 — STILL OPEN (seed defect, not fixable in .spl)

Binary identity: `readlink -f bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`;
`stat -c '%s %y'` -> `59537240 2026-08-17 12:58:51.339525019 +0000`.

Repro (`r5.spl`, the `first3` / `get3` rows):

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r5.spl
first3=3
get3=3
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r5.spl
first3=-1
get3=-1
```

Reproduces exactly as filed. The accessor exemption list is confirmed still
present at
`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1815-1822`
(`"first" | "last" | "get" | "min" | "max" | "pop" | "remove" | "at"`, inside
`lower_coalesce` which begins at `:1774`).

**Not fixed here:** Rust bootstrap seed, and the record's own analysis is that
the correct fix is the `seed_hirtype_optional_plan.md` work (accessor result
must carry a distinguishable `T?` with a BOXED payload across the JIT call
boundary), not a local patch — suppressing the nil check for these accessors
would trade this bug for the strictly worse `[].first() ?? -1` leak. Not
attempted; standing workaround unchanged.

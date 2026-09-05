# JIT: `if val x = opt` sugar and `??` leak the raw boxed-Some representation

**Status:** OPEN. Found 2026-08-17 by the class-detection half of
`test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl`,
while confirming
`native_optional_tuple_payload_extraction_broken_2026-07-29.md` as already
fixed.

**Severity:** HIGH — silent wrong results on the DEFAULT engine
(`bin/simple run`, Cranelift JIT). No crash, no diagnostic, rc=0.

## Symptom

An optional holding a **boxed** `Some` (a real heap enum, as produced by a
literal `Some(x)` construction) is consumed correctly through the *pattern*
spellings and incorrectly through the *sugar* spellings.

Fixture (`fn f() -> i64?: Some(99)`), `SIMPLE_EXECUTION_MODE=jit`:

| spelling | interpreter | JIT | verdict |
|---|---|---|---|
| `match f(): Some(e): print e` | 99 | 99 | OK |
| `if val Some(e) = f(): print e` | 99 | 99 | OK |
| `if val e = f(): print e` | 99 | **3676701660481** | WRONG — raw enum pointer |
| `print f() ?? 0` | 99 | **792** | WRONG — `99 << 3`, un-unboxed BoxInt |
| `print f()` | `Option::Some(99)` | **3676701660481** | WRONG — raw enum pointer |

`if val e = Some(99)` inline prints `<enum@0x3322a7f1120>`; the same shape with
a `text` payload prints `<enum@0x211c6801e00>`, so it is not type-specific.

The **raw migration form** (`fn f() -> i64?: 99`, no `Some` wrapper) is correct
on every spelling — only the boxed representation is affected.

## Root cause

`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1871-1874` and
`:2177-2181` lower the bare-`if val` unwrap sugar and the `??` coalesce to a
single `rt_unwrap_or_self` builtin call. That builtin handles *presence*
discrimination for both representations, but the two representations need
**different post-processing**: a boxed payload is BoxInt'd and depends on the
name-keyed `UnboxInt` special case in MIR's `lower_builtin_call_expr`, while a
raw value must pass through untouched. `rt_unwrap_or_self` gets neither, so the
boxed arm returns the un-unboxed word — the enum pointer, or `99 << 3 = 792`.

This is exactly the failure mode predicted by the row-1 bug doc, which recorded
that "a different builtin alone (e.g. `rt_unwrap_or_self`) is NOT sufficient …
swapping the builtin regressed a literal `Some(99)` binding to 792 = 99<<3".
The *pattern* path took that advice and emits a runtime `rt_enum_id(subj) >= 0`
discrimination branch
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:1396-1429`); the
sugar path in `control.rs` never did.

## Fix direction

Give the sugar/coalesce lowering the same runtime discrimination branch the
pattern path already has, rather than a single representation-agnostic builtin:

```
if rt_enum_id(subj) >= 0: rt_enum_payload(subj)   # boxed — BoxInt + name-keyed UnboxInt
else:                      subj                    # raw — pass through
```

Both sites in `control.rs` need it. Do not "fix" this by changing
`rt_unwrap_or_self`'s runtime behaviour — the post-processing difference lives
in MIR lowering, not in the builtin.

## Coverage

`test/01_unit/compiler/codegen/probe_optional_payload_extraction_jit.spl` (the
run-path probe) reports, on the currently deployed seed:

```
FAIL boxed_ifval_sugar got=6363070744225 want=99
FAIL boxed_coalesce got=792 want=99
OPTIONAL_PAYLOAD PROBE: FAILURES=3
```

against `OPTIONAL_PAYLOAD PROBE: ALL PASS` on the interpreter. The spec above
is RED by design until this lands.

## Unresolved

The probe's third failure, `FAIL ifval_scalar_f64 got=576601489791778816
want=2.5`, reproduces only in the full multi-function probe; the same `f64?`
extraction in an isolated two-function file is correct on the JIT. Not yet
isolated — it may be a separate f64-tagging defect or a demotion artefact of
the smaller file. Filed here rather than dropped, but NOT root-caused.

## Out-of-scope note

`src/compiler_rust/compiler/src/hir/lower/expr/control.rs` was not owned by the
session that found this (file ownership was limited to `stmt_lowering.rs` and
`codegen/jit.rs`), so no patch was attempted. Reported, not fixed.

## Re-verified 2026-08-17 — STILL OPEN (seed defect, not fixable in .spl)

Binary identity: `readlink -f bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`;
`stat -c '%s %y'` -> `59537240 2026-08-17 12:58:51.339525019 +0000`.

Repro (`r2.spl`: `fn f() -> i64?: return Some(99)`, then `if val e = f(): print e`
and `print f() ?? 0`):

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r2.spl
99
99
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r2.spl
5338887559137        <- raw enum pointer (bare `if val` sugar)
792                  <- 99 << 3, un-unboxed BoxInt (`??`)
```

Both wrong values reproduce exactly as filed (the pointer differs run to run,
as expected). Cited sites confirmed at slightly shifted lines: the two
`rt_unwrap_or_self` builtin emissions are
`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1874` (bare `if val` /
coalesce then-branch unwrap) and `:2242`.

**Not fixed here:** defect is in the Rust bootstrap seed, out of scope for a
pure-Simple fix. The filed fix direction (emit the `rt_enum_id(subj) >= 0`
discrimination branch that `stmt_lowering.rs` already has, at BOTH sites) still
stands and was not attempted.

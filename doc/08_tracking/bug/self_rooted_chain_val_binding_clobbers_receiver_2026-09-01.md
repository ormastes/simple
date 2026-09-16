# Interpreter: `val x = self.<field>.<call>().<call>()` clobbers `self` with the chain's tail value

**Date:** 2026-09-01 · **Status:** OPEN · **Severity:** blocker (aborted every MCP native build at HIR entry)

## Symptom

Binding a self-rooted, three-hop call chain to a `val` leaves the frame's
`self` bound to the chain's TAIL value. Every later `self.<field>` in that
frame then fails, and the diagnostic names the tail's return type:

```
undefined field 'marker': cannot access field on value of type 'bool'
undefined field 'marker': cannot access field on value of type 'i64'
undefined field: unknown property or method 'marker' on String
```

## Minimal reproduction (unit scale, no compiler closure required)

`test/01_unit/compiler/self_receiver_chain_member_access_spec.spl`
(`@tag:in-development` — encodes the correct contract, expected to fail).
Measured on seed `src/compiler_rust/target/release/simple.exe`
md5 `286f66b8615dce0e0da788f0550c4008`, `SIMPLE_EXECUTION_MODE=interpret`:
**7 examples, 4 failures.**

```
class Root:
    var mid: Mid = Mid()
    var marker: text = "root"

    me tail_bool() -> text:
        val flag = self.mid.get_leaf().positive()   # field hop + 2 calls
        return self.marker                          # FATAL: self is `false`
```

## What does and does not trigger it

| form | result |
|---|---|
| `val x = self.a.m1().m2()` then `self.f` | **CLOBBERS** (bool, i64 and text tails all reproduce) |
| `if self.a.m1().m2():` then `self.f` | safe |
| `self.a.m1().m2()` as a bare trailing return expression | safe |
| the same chain inside a `while` loop, result used in an `if` | safe |
| `val y = self.a.m1()` then `val x = y.m2()` (split) | safe — this is the workaround |
| two-hop `self.a.m1()` bound to a `val` | safe |

So the trigger is specifically **binding a >=2-call self-rooted chain to a
`val`**, not the chain itself.

## Production impact (how it was found)

`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:347`

```
val already_bound = self.symbols.lookup_or_invalid(local_name).is_valid()
val imported_type = self.symbols.define(...)     # <-- fatal
```

aborted `native_build_worker` on `src/app/mcp/main.spl` at step 2/6 (`hir`),
module 0, after ~21 minutes of parse + surface_build, with
`error: semantic: undefined field 'symbols': cannot access field on value of
type 'bool'`. Pinned by inserting an `eprint` probe before every
`self.symbols` in the method: the line-347 probe fired exactly once and the
fatal followed immediately, while the single-hop siblings on lines 238 and
449 ran 33 and 541 times cleanly. `SIMPLE_DEBUG_FIELD_ACCESS=1` reported
`field=symbols recv_type=bool recv=false expr=Identifier("self")`.

## Workaround applied

The three `val already_bound = self.symbols.lookup_or_invalid(...).is_valid()`
sites (lines 347, 367, 436 — enum / trait / type-alias branches) were split
into a typed intermediate `val`. The four `if <chain>:` sites in the same file
(538, 581, 789, 888) were deliberately left alone: the table above shows that
form is not affected, and changing them would be noise.

## Still to do

Fix the interpreter so the write-back does not happen, then drop
`@tag:in-development` from the spec. The `.spl` split is a workaround, not the
fix — the same shape almost certainly exists elsewhere in the compiler and in
userland, silently.

## Related
- `doc/08_tracking/bug/mcp_native_build_hir_entry_env_get_nil_len_fatal_2026-09-01.md`
- `.claude/rules/language.md` § Runtime Limitations, "Chained methods on erased receivers"
- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:587` ("staged aggregate-receiver accessor hazard")

## Spec status caveat (measured 2026-09-01)
`test/01_unit/compiler/self_receiver_chain_member_access_spec.spl` carries
`# @tag:in-development`, but **that tag is not wired at this tree**: a repo-wide
grep for the literal `in-development` in `src/**.spl` returns exactly two hits,
both prose — `src/app/tag_query/main.spl:17` and a comment at
`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:196`. The
`in_development` counter field exists and is copied around
(`test_runner_execute.spl:944`, `test_runner_mcdc_report.spl:249`) but nothing
sets it from the tag. So the file reds a whole-suite run today (7 examples,
4 failures). Left red deliberately — the failures ARE this defect. Promote to
green by fixing the interpreter, not by weakening the assertions.

# JIT: `Ok(None)` of `Result<T?, text>` matches neither `Ok(Some(x))` nor `Ok(None)` arm

Status: open. Observed 2026-11-27, seed `simple-local-20261127m`, JIT coordinator (`native-build` coordinator, `hybrid-interp-splice` demotion lines present).

Observed instance: `src/app/compiler_entrypoint/inventory_events.spl` cold-init scan, for the skipped path
`examples/10_tooling/README.md`, `_compiler_inventory_event_for_path_cost_v1(...) -> Result<CompileSourceEventV1?, text>` returned
`Ok(None)` (line 206/213) and
```
match f(...):
    case Err(_): return None
    case Ok(Some(ev)): events.push(ev)
    case Ok(None): ()
```
aborted with `invalid pattern: match statement exhausted without matching any pattern (no arm matched)`.

Candidate minimal repro — does NOT reproduce (run 2026-11-27 on seed simple-local-20261127l, `skip` renamed to `empty` since `skip` is a keyword): prints `none` under both `SIMPLE_EXECUTION_MODE=jit` and `interpret`. The observed failure needs the real shape (struct payload `CompilerInventoryEventV1?` inside `Result`, inside the inventory scan loop); a reproducing minimal case is still owed.
```
fn f(empty: bool) -> Result<i64?, text>:
    if empty: return Ok(None)
    Ok(Some(1))
fn main():
    match f(true):
        case Err(_): print "err"
        case Ok(Some(v)): print "some {v}"
        case Ok(None): print "none"
```
Run with `SIMPLE_EXECUTION_MODE=jit`; expected `none`.

Workaround applied: `case Ok(item): if item.is_some(): ... item!` (two sites in inventory_events.spl). Root fix belongs in the
JIT/interpreter pattern matcher for nested Option inside Result.

## Root cause and fix (2026-11-27, seed `simple-local-20261127s`)

Reproduced on seed `r` with a decoy: any user enum in the flattened module that declares a `None` (or `Some`)
variant. The i64 candidate above did not reproduce because its module has no such enum; the SCV closure does.

```
# decoy.spl
enum Mode:
    None
    Fast
# prod.spl:  pub fn pick(empty: bool) -> Result<Ev?, text>: ... return Ok(None)
# main.spl:  match pick(true): case Err(_): ... case Ok(Some(ev)): ... case Ok(None): ...
```
`SIMPLE_EXECUTION_MODE=jit` -> `match expression exhausted without matching any pattern`; interpret -> fine.

Cause: `subpattern_condition_typed` (`hir/lower/expr/control.rs`) gated the nested builtin-optional path
(`rt_is_none` / `rt_is_some`) on `is_builtin_optional_variant_name`, a MODULE-wide name test that is false as soon as any
non-`Option` enum in the module has a `None`/`Some` variant. `Ok(None)` then fell to the discriminant test
`rt_enum_check_variant(slot, OPTION_ID, NONE_DISC)`, which is false on the raw-nil form the producer builds, so every arm
rejected it and the fail-closed exhaustion panic fired. MIR diff (`SIMPLE_DUMP_MIR=<fn>`) showed exactly that call.

Fix: the nested arm now also takes the presence/absence path when the slot's static type is the builtin `Option<T>`
enum or a `T?` pointer (`slot_is_builtin_option`), unless the pointee is an enum owning that variant name.
Regression test: `compiler/tests/jit_nested_option_result_user_none_enum_match.rs`.
Both inventory_events.spl sites (247 expression form, 474 statement-in-loop form) share the same lowering.

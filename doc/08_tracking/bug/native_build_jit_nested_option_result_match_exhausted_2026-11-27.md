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

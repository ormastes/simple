# Interpreter: Dict values corrupted inside struct under copy-return semantics

**Date:** 2026-07-03
**Severity:** high (silent data corruption)
**Status:** CLOSED 2026-08-01 — fixed by `61bfb659210`; the 8x figure was a
misattribution. See "Closure" at the end.

## Symptom

A `Dict<text, i64>` embedded in a **struct** returns corrupted values when the
struct is passed through copy-return (value-semantics) functions. Probe:

```simple
struct Box:
    data: Dict<text, i64>

fn box_set(b: Box, k: text, v: i64) -> Box:
    var nb = b
    nb.data[k] = v
    nb
```

Stored `42` reads back `336`; stored `7` reads back `56` — a consistent 8x
scaling artifact, suggesting a pointer/width confusion when the Dict is copied
as part of the struct value.

## Not affected

`class Sheet` with `cells: Dict<text, Cell>` works — classes use mutation
(reference) semantics, so the Dict is never value-copied.

## Workaround (in production use)

Parallel arrays instead of Dict-in-struct where copy semantics are required:
`src/app/office/sheets/cell_format.spl` (`SheetFormats { keys: [text],
specs: [FormatSpec] }` with linear scan). Same idiom as `[CondRule]` in
`cond_format.spl`.

## Related known issues

- Struct default-field omission corrupts all field reads in interpreter mode
  (found during array-formula work, 2026-07-03).
- Same-name struct in two modules collides in the global registry.
- Aggregates through function params lose mutations (return-the-object rule).

## Next step

Reproduce in a minimal interpreter test (`Dict` copy path in
`src/app/interpreter/` value cloning); the 8x factor points at element-size
(byte-vs-slot) confusion when cloning Dict storage embedded in a struct value.

## 2026-07-20 addendum: total-loss variant (no corruption, mutation vanishes)

Found via `test/feature/plugin/plugin_startup_block_spec.spl` (whole-suite
triage campaign, `plugin_startup`/`sugar_plugin`/`runtime_api_plugin` cluster).
Same root shape (`struct` with a `Dict<text, Any>` field, mutated through a
`me register(self, ...)` method), but the failure mode here is total loss
rather than 8x scaling corruption:

```
struct BlockRegistry:
    blocks: Dict<text, Any>

impl BlockRegistry:
    me register(self, block_def: Any):
        val kind = block_def.kind()
        self.blocks[kind] = block_def   # src/compiler/15.blocks/blocks/registry.spl:67-69

fn register_block(block_def: Any) -> bool:
    val kind = block_def.kind()
    if is_block(kind):
        return false
    var reg = block_registry()   # copy of the Option<BlockRegistry> singleton payload
    reg_register(reg, block_def) # mutates the LOCAL copy `reg` only
    true                          # _global_registry is never reassigned
```

`register_block(...)` reliably returns `true` (no crash, no wrong-scaled
value), but the mutation never reaches the `_global_registry` singleton:
`is_block(kind)` is still `false` immediately afterward. Minimal repro run
via `bin/simple run` on the deployed self-hosted binary
(`bin/release/x86_64-unknown-linux-gnu/simple`):

```
register_block returned: true
activate_plugin returned: true
is_block after: false
```

Two `it` blocks in `plugin_startup_block_spec.spl` pin this exact contract
and fail as a direct result:
- "activate_plugin fires hook and registers block via real registry" —
  `expect(ok).to_equal(true)` sees `false` (the pure-Simple plugin hook
  `csv_setup()` calls `register_block`, which reports success but the
  registry never actually gains the entry, so the two-phase contract cannot
  be verified end-to-end).
- "register_block returns false for already-taken keyword" — the second
  `register_block` call for the same keyword also returns `true` (expected
  `false`), because `is_block(kind)` on the still-unpersisted registry never
  sees the "already registered" state from the first call either.

This is exactly the "Aggregates through function params lose mutations
(return-the-object rule)" item already listed under "Related known issues"
above, now confirmed concretely for `BlockRegistry`'s `Dict`-in-`struct`
global-singleton pattern. Likely one-line fix once someone owns this class of
bug generally (not applied here — out of scope for the triage task that found
it): `register_block` should reassign `_global_registry = Some(reg)` after
`reg_register(reg, block_def)`, or `BlockRegistry` should become a `class`
(reference semantics) matching the "Not affected: `class Sheet` ... works"
note above.

Affected spec: `test/feature/plugin/plugin_startup_block_spec.spl` (2 of 3
examples fail; left unmodified per the "never weaken an assertion" rule — the
spec is asserting the correct/intended two-phase contract).

## Closure 2026-08-01

Does not reproduce. 18 checks across 7 probes and 2 engines, 0 failures. The
doc's verbatim probe outputs `a=42 / b=7 / keys=2` on both, with no 8x scaling:

```
src/compiler_rust/target/bootstrap/simple run <probe>.spl              # JIT
SIMPLE_NO_JIT=1 src/compiler_rust/target/bootstrap/simple run <probe>.spl   # interpreter
```

Also correct: `.get()` vs `[k]` (both 42/7), the 3-hop `root.inner.data[k]`,
composite tuple dict keys, and both ADR-004 shapes.

**Fixed by `61bfb659210`** (2026-07-27, "real place model - two-hop mutation
loss FIXED, oracle 5/4 -> 5/0"). `nb.data[k] = v` is a two-hop place —
`Projection::Field("data")` then `Projection::Index(k)` — handled by `step_mut`
(`src/compiler_rust/compiler/src/interpreter/place.rs:130-157`) and
`store_last` (:173+). `Arc::make_mut` is correct CoW here: `var nb = b` makes
the Arc non-unique, so the write deep-copies and `b` is untouched.

**The 8x figure was misattributed.** 42 -> 336 and 7 -> 56 is `value << 3`, the
known tag-box artifact, not a Dict-in-struct defect. Filing it under this bug
sent the investigation at the wrong subsystem.

**ADR-004 does NOT cover the primary shape.** ADR-004 is scoped to indexed
access YIELDING A VALUE, and explicitly rules that compound-assignment lvalue
paths like `nb.data[k] = v` "are writes to an lvalue, not method calls on a
temporary, and stay valid" — which is exactly this doc's probe. Invoking it
here would be wrong. The 2026-07-20 addendum (total-loss) shape IS an ADR-004
case and is already fixed in source at
`src/compiler/15.blocks/blocks/registry.spl:151-153`, whose write-back cites
ADR-004 by name.

**No regression spec added, deliberately.** It would be vacuous: no available
binary fails it. `simple_seed` (Jul 25, PREDATING the Jul-27 place fix) passes
the probes too, so the Dict-in-struct shape was never broken by the two-hop
defect. `simple.jul7-segv-bak` core-dumps without a signal. The test-runner
lane — the engine ADR-004 documents as the losing one — was unmeasurable: three
`simple test` runs and a `compile --native` all hit RC=124 at 900s under load
~80, because `simple test <path>` walks the whole shared tree and that tree is
full of other sessions' parse errors. A guard that pins nothing is worse than
no guard, so none was written.

Engine caveat: the pure-Simple ObjectStore interpreter is NOT exercisable at
HEAD — `bin/simple` has no `run`/`test`, and `simple.pre-segv-fix-20260731`
prints the Rust-seed banner, so it is a seed build too. Every engine reachable
here is the Rust seed.

Follow-up, not done here: the `cell_format.spl` parallel-array workaround is no
longer required.

# BUG: JIT struct assignment ALIASES instead of copying (interpreter copies)

> **MOSTLY RESOLVED 2026-08-10 — stale-binary measurement.** The binary
> measured below (deployed 2026-08-09 04:50) predates the F1 campaign that
> landed later the same day: `735bbd4b606` (S3: carry struct-vs-class
> declaration kind into seed HIR/MIR), `cf992112a2d` (S5: `MirInst::
> AggregateCopy` primitive + copy sites F–I in
> `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` /
> `lowering_core.rs::copy_if_value_type`), `9106761fe76` (S6: struct param
> copy site J). Re-run on a fresh seed (`src/compiler_rust/target/release/
> simple`, 59,000,784 B, 2026-08-10 04:16): plain assignment, argument,
> return, list-element and dict-value extraction now COPY under the JIT,
> matching the interpreter (probe printed 1.0 in all five, CONTROL=42).
>
> **RESIDUAL item 1 FIXED 2026-08-10.** `MirInst::AggregateCopy` gained a
> `deep_fields: Vec<AggregateFieldCopy>` descriptor, built at MIR lowering
> (`lowering_core.rs::struct_deep_fields`, gated by the same fail-closed
> `type_value_kinds == Some(true)` check as the outer copy, with a
> visited-type-name path guard + depth cap 16 for termination on
> self-referential shapes) and consumed recursively by both backends
> (`codegen/instr/closures_structs.rs::emit_aggregate_block_copy` for
> Cranelift/JIT, `codegen/llvm/functions/objects.rs::
> emit_aggregate_block_copy` for LLVM/AOT). `var o2 = o; o2.inner.a = 33.0`
> now leaves `o.inner.a` at its original value under both interpreter and JIT
> (verified via `test/03_system/language/value_semantics/probe/
> p2_nested_struct_field.spl`: interp and JIT both print `S2b o.inner.a=99.0
> o2.inner.a=33.0`). Sabotage-tested: forcing `deep_fields` to `&[]` at the
> Cranelift call site (`codegen/instr/mod.rs`) reproduces the exact original
> divergence (`o.inner.a=33.0` under JIT vs `99.0` under interp), confirming
> the fix — not a coincidental pass — closes the gap. Arrays and text are
> deliberately NOT deep-copied through this path (already correct on every
> engine; would add a perf cliff). Perf cost measured on a 300k-iteration
> struct-copy-with-nested-field microbenchmark: ~100ns/copy added for one
> nested field (0.157s deep vs 0.127s shallow-only, same binary) — not
> alarming.
>
> **RESIDUAL (still open):**
> 2. **`m[1][0] = 9` divergence unchanged**: interpreter rejects
>    (`interpreter/node_exec.rs:1481`, final `else` of a chain whose wording
>    — "nested field access not fully supported" — reads as an unimplemented
>    gap, not a deliberate restriction; nothing in doc/ says it is intended),
>    JIT lowers it fine (`mir/lower/lowering_stmt.rs:490` lowers the receiver
>    expression first). ADR-004 says compound-assignment lvalue writes "stay
>    valid", so the interpreter is the nonconforming side.
> 3. **AOT lane now has a concrete blocker**: `native-build` of even the
>    minimal struct probe fails with `llc-20: void type only allowed for
>    function results` (invalid LLVM IR emission). AOT struct semantics
>    remain unmeasured.
>
> Deployed `bin/release/x86_64-unknown-linux-gnu/simple` is STALE w.r.t. all
> of this until redeployed from a post-`9106761fe76` build.

- Date: 2026-08-10
- Severity: HIGH (silent cross-engine semantic divergence; corrupts any code
  that assigns a struct and mutates the copy)
- Engines: JIT (bare `bin/simple foo.spl`) WRONG; interpreter
  (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) correct per the
  documented value-type ruling. Binary at measurement:
  `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed).
- Full truth table + probe source:
  `doc/07_guide/language/value_semantics_by_engine.md`

## Repro (minimal)

```
struct Flat:
    a: f64
    b: i64

fn main():
    var f = Flat(a: 1.0, b: 2)
    var f2 = f
    f2.a = 7.0
    print("f.a={f.a}")   # interpreter: 1.0   JIT: 7.0

main()
```

The aliasing is systemic, not assignment-only. Under JIT, mutating a struct
obtained via ANY of these positions mutates the original:

| Position | Interp (copy) | JIT (alias) |
|----------|---------------|-------------|
| `var f2 = f` | orig 1.0 | orig 7.0 |
| copy of struct containing nested struct | orig unchanged | orig changed |
| function argument, callee writes field | orig 1.0 | orig 55.0 |
| returned struct, copy, mutate copy | orig 1.0 | orig 88.0 |
| `var e = lst[0]; e.a = ...` | lst 1.0 | lst 77.0 |
| `var de = d["k"]; de.a = ...` | dict 1.0 | dict 44.0 |

Arrays and text COPY in both engines (verified same run), so this is
struct-specific.

## Secondary divergence (same probe)

`m[1][0] = 9` (nested index assignment) is a semantic error in the
interpreter — `invalid assignment: index assignment requires identifier or
field access as container` — but compiles and works under JIT. One engine
must be wrong; either the interpreter should accept it or the JIT should
reject it.

## Impact

- Any prior measurement of "value semantics" performed with bare
  `simple foo.spl` measured the JIT and concluded ALIAS; measurements via
  the interpreter concluded COPY. Both were faithfully reporting their lane
  (explains the `ca750206e0c7` vs `197b61f972f` contradiction).
- Code written against interpreter semantics (defensive copy-then-mutate)
  silently corrupts originals when run under the default JIT lane.

## Native/AOT lane

NOT MEASURED — two `native-build` attempts of the probe (300s / 550s, second
with `SIMPLE_TIMEOUT_SECONDS=3600`) emitted nothing and produced no binary on
a host saturated by concurrent stage3 builds. The AOT behaviour for struct
assignment is unknown and must be measured separately.

## Expected

If the language intends value semantics for structs (consistent with the
text/array rulings and interpreter behaviour), the JIT must copy structs on
assignment, argument passing, return, and container extraction.

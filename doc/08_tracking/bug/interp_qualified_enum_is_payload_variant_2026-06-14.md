# interp_qualified_enum_is_payload_variant

- **ID:** interp_qualified_enum_is_payload_variant
- **Severity:** P1 (silent wrong result)
- **Status:** resolved (2026-06-14)
- **Date:** 2026-06-14
- **Component:** interpreter / seed (`src/compiler`)

## Resolution (2026-06-14)

The `bin/simple run` path uses the Cranelift JIT (not the tree-walker); MIR
lowering emitted `BinOp::Is` as a raw pointer `icmp` of two distinct heap
allocations, so it was always false. Fixed in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`: when the RHS is
an enum-variant global (`E.A` or called `E.A()`), lower `is` to
`rt_enum_check_discriminant(value, hash(variant)&0xFFFFFFFF)` — the same check
`match` uses. The tree-walk interpreter path (`interpreter/expr/ops.rs`) got the
matching discriminant-only fix. Verified: `a is E.A` → true (payload variant),
`b is E.B` → true (unit), cross-variant → false, `match` non-regressed. Requires
seed rebuild to deploy.

## Symptom

The qualified enum-variant test `value is EnumName.Variant` evaluates to **false**
even when `value` is a freshly constructed instance of that exact variant — at
least for payload-carrying variants. This silently routes `if … is …` /
`else if … is …` chains into their `else` branch.

## Minimal repro (seed driver)

```simple
enum E:
    A(x: i64)
    B

fn main():
    val a = E.A(x: 5)
    val r = if a is E.A: "isA" else: "notA"
    print(r)        # prints "notA"  (expected "isA")
```

By contrast, `match a: case E.A(x): ...` matches and binds correctly. The
unqualified form `a is A` does not parse (`variable 'A' not found`).

## Impact

Root cause of `wal_disk_replay_blank_row` (P0): DBFS `MetaStore` journal
serialization used `entry.op is MetaOp.Variant` chains, so every op fell through to
the `CHECKPOINT`/empty-payload `else`, dropping all field data on disk.

## Workaround

Discriminate payload-carrying enums with `match` (works) or, for payload-less
variants, `==`. The `wal_disk_replay_blank_row` fix swapped the broken `is`-chains
in `meta_store.spl` for `match`.

## Proper fix (pending)

Make `value is EnumName.Variant` evaluate true for matching payload-carrying
variants in the interpreter, consistent with `match`. Fix is in the seed/compiler
(`src/compiler`), not in `.spl` library code.

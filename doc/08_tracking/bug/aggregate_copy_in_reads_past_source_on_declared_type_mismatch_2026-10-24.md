# Aggregate copy-in reads past the source object when the declared type is larger than the actual one

- **Date:** 2026-10-24
- **Status:** OPEN — found by audit, not yet observed as a crash. Filed because the
  enabling mismatch IS observed live in a real Stage 2 build log.
- **Files:** `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`,
  `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`,
  `src/compiler_rust/compiler/src/mir/inst_enum.rs`,
  `src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs`
- **Related:** `cranelift_cmov_memory_operand_unconditional_load_2026-10-23.md`
  (same function, different trigger — that one is an `Option` in a struct-typed
  slot; this one needs no `Option` at all)

## The gap

`emit_aggregate_block_copy` sizes its copy from the **declared** type and never
checks the source object's actual size.

```rust
let words = byte_size.div_ceil(8).max(1);        // :697  declared byte_size only
let new_ptr = call_runtime_1(ctx, builder, "rt_alloc", size_val);   // :701
// validity: tagged heap pointer, non-null -- says NOTHING about size   :705-711
let load_ptr = builder.ins().select(src_is_valid, src_ptr, new_ptr); // :759
for w in 0..words {                                                  // :761-766
    let word = builder.ins().load(types::I64, MemFlags::new(), load_ptr, off);
    ...
}
```

`src_is_valid` asks only "is this a tagged, non-null heap pointer". So whenever
it is true, the loop reads `words` words from `src_ptr`, with `words` derived
from the declared type.

**The existing bound does not help.** The `deep_fields` loop has:

```rust
if word_index >= words { continue; }   // :771-773  "descriptor out of range"
```

but `words` comes from the same declared `byte_size`, and this guard reads from
`new_ptr` (`:774`), the destination codegen itself sized. It protects the
destination buffer. The over-read from `src_ptr` already happened upstream at
`:761-766`, so this check cannot retroactively prevent it.

`byte_size` traces to `copy_if_value_type` (`lowering_core.rs:1022`):

```rust
let byte_size = (fields.len() as u32) * 8;
```

computed from a registry type supplied by the call site — a **declared** type,
independent of the runtime value's own type.

## Why a mismatch reaches codegen at all

`validate_declared_return_type` (`function.rs:342-368`) **downgrades** a
declared-vs-actual return type mismatch to a warning whenever either side is an
aggregate, and returns `Ok(())`:

```rust
if downgrade_to_warning {
    eprintln!("warning: declared return type mismatch admitted (seed aggregate typing not authoritative): ...");
    return Ok(());
}
```

The rationale given there is legitimate — the seed's aggregate typing diverges
from the self-hosted reference in "trailing `match` arm unification, cross-module
re-registration, ANY-field fallback copies", and making it fatal rejected 542
valid files the day the check landed. The consequence, though, is that
mismatched aggregate types survive into MIR and codegen.

## This is observed, not hypothetical

A real Stage 2 `native-build` log (`--backend=cranelift`, x86_64, 2026-10-24)
emitted these admitted mismatches, among 11 in a partial run:

| expected | found |
|---|---|
| `Struct IncrementalCompileResult` (2 fields) | `Struct IncrChangeSet` (1 field) |
| `Struct ISelInstResult` | `Tuple([])` |
| `Enum Result<T,E>` | `Array { element, size: None }` |
| `Bool` | `Tuple` |

The first row is the dangerous shape. Concretely, with no vtable:

- declared `IncrementalCompileResult`, 2 fields -> `byte_size = 16` -> `words = 2`
- `rt_alloc(16)` for `new_ptr` — correct for the declared type
- actual object is an `IncrChangeSet`, 1 field -> real allocation **8 bytes**
- the loop reads **2 words = 16 bytes** from `src_ptr` -> the second read is
  **8 bytes past the end of the actual allocation**
- that out-of-bounds word is stored at `new_ptr+8`
- `IncrementalCompileResult`'s descriptor for its 2nd field has `word_index = 1`;
  `1 >= 2` is false, so it is **not** skipped
- the deep-field loop loads that garbage word back out and, if its low 3 bits
  happen to be `1` and the untagged part is nonzero, recurses on it as a live
  heap handle -> wild dereference

That is the same end mechanism as the sibling record, reached without any
`Option` being involved.

## Second finding: `owner_has_vtable == None` is not treated as `Some(false)`

`inst_enum.rs:25-26` documents the contract:

> `None` until that pass runs (e.g. single-file/non-native-project compiles);
> codegen must treat `None` the same as `Some(false)`.

Codegen does something else (`closures_structs.rs:690-691`):

```rust
let has_vtable = owner_has_vtable
    .unwrap_or_else(|| type_name.is_some_and(|n| ctx.vtable_data_ids.contains_key(n)));
```

For `None` it consults a per-compilation-unit map, which can answer **true**. The
comment above it says this is deliberate ("only unresolved JIT layouts may infer
the header from the local map"), so the discrepancy is between the two comments,
not obviously a bug — but one of them is wrong and a reader following
`inst_enum.rs` will mispredict codegen. Recording it so the contract gets
reconciled rather than rediscovered.

**Operational consequence, which already cost this lane time:** the resolver
`qualify_native_struct_layouts` (`pipeline/native_project/compiler.rs:1984`) has
exactly one non-test caller, `:829`, inside the native-project pipeline. It does
**not** run for single-file/JIT compiles. So a JIT probe leaves
`owner_has_vtable == None` and goes through the local-map heuristic — a different
descriptor path than a native build. **A JIT probe is therefore not valid
evidence about native aggregate-copy behaviour**, which is why two
payload-binding probes passing under JIT did not clear the native path for the
sibling bug.

## Not established

- The exact call site feeding the `IncrementalCompileResult`/`IncrChangeSet`
  mismatch into `copy_if_value_type` was not traced end to end; the audit was
  fenced to the four files above and the candidate sites live in
  `lowering_stmt.rs`/`lowering_expr_struct.rs`. Nothing in the audited files
  prevents the path.
- Whether any field type occupies other than one 8-byte slot. `struct_deep_fields`
  assumes one word per field (`word_index: i as u32` at `:1084`,
  `byte_size: (inner.len()) * 8` at `:1087`) with no per-field width computation.
  No counterexample was found in the audited files, but `StructInit` /
  `effective_field_offset` are the authority and were out of scope.
- No crash has yet been attributed to THIS trigger. The over-read is established
  from the code; the resulting fault is not.

## Why the obvious fix is wrong

Narrowing `src_is_valid` is not available. `emit_aggregate_block_copy` ends
(`:795-799`):

```rust
let tagged_new_ptr = builder.ins().bor(new_ptr, heap_tag);
builder.ins().select(src_is_valid, tagged_new_ptr, src_tagged)
```

An invalid source returns `src_tagged` **unchanged**, so the "copy" becomes an
alias of the original — `var b = a; b.x = 1` would mutate `a`. PR #4239 was
withdrawn for exactly this reason. A fix needs the source's real size (a header,
or a descriptor that carries the allocation size), or it needs the type mismatch
not to reach codegen.

# Shared root cause: the interpreter merges shared collections on the ARGUMENT boundary only, never on the RETURN boundary

- **Date:** 2026-08-17
- **Severity:** P1 — silently wrong results, no diagnostic
- **Root cause:** `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:1203`
- **Status:** FIXED for the struct/self-field sibling (re-verified 2026-11-03); enum-payload residual split to `enum_payload_dict_copied_on_function_return_2026-07-28` (still OPEN).

## The mechanism

`merge_shared_collection_fields` (`function_exec.rs:1016`) propagates
`Array` / `Dict` / `ByteArray` fields from callee back to caller, recursing
through nested `Value::Object` so a by-value receiver's nested containers still
reach the caller. It is correct as far as it goes.

It has exactly one live call site — line 1203, inside
`write_back_mutable_arguments` (line 1070). Verified:

```
$ grep -n 'merge_shared_collection_fields' function_exec.rs
1016:fn merge_shared_collection_fields(caller_val: &mut Value, callee_val: &Value) {
1041:                merge_shared_collection_fields(&mut merged, new_field);   # self-recursion
1203:                            merge_shared_collection_fields(&mut caller_val, callee_val);
```

So the merge runs when a container arrives as an **argument**. Nothing merges a
container that leaves through the **return value**. There is no return-side
equivalent anywhere in the file.

Two further limits of the existing function, both relevant:

- it early-returns unless **both** sides are `Value::Object`
  (`function_exec.rs:1017-1021`), so an **enum** carrying a `Dict` payload never
  reaches it at all;
- it is keyed on struct field names, so a bare returned container has no slot to
  merge into.

## Evidence — the passing and failing siblings are the proof

From one run of `test/01_unit/compiler/interpreter/self_field_assign_spec.spl`
(binary `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37):

```
✗ preserves self.field mutations passed through free functions
    expected 1 to equal 11
✓ preserves self receiver mutations passed through free functions
✓ preserves mutations through free functions whose parameter is named self
✓ preserves dictionary-field mutations through free functions
✗ preserves struct dictionary-field mutations through returning free functions
    expected subject to be truthy, got false
✓ keeps self bound when its field is passed after an extern call
SPEC FILE VERDICT: ... declared>=13 executed=13 passed=11 failed=2 dropped=0
Results: 13 total, 11 passed, 2 failed
```

Read the pair together:

| example | boundary | verdict |
|---|---|---|
| `preserves dictionary-field mutations through free functions` | argument | **passes** |
| `preserves struct dictionary-field mutations through **returning** free functions` | return | **fails** |

Same data, same containers, differing only in which boundary the value crosses.
That is the defect stated as a controlled experiment, and it matches the code:
the argument path has a merge, the return path does not.

## Rows this collapses

- `enum_payload_dict_copied_on_function_return_2026-07-28.md` — its own summary
  says the copy "is caused by the **return boundary**, not by the dict literal,
  not by the method call, and not by the `match`", and its probe table shows the
  in-caller-frame variant (L) persisting while all three
  returned-from-a-function variants (K, M, N) do not. Reproduced:
  `test/01_unit/lib/common/sdn_coverage_spec.spl` fails exactly the example the
  doc names as its discovery case — `✗ get by key from dict, expected true to
  equal false` — `Results: 71 total, 70 passed, 1 failed`.
- `struct_dict_field_mutation_engine_divergence_2026-08-10.md` — the
  `self_field_assign_spec.spl` failures quoted above.

## Correction to BRIEF correction #2

The BRIEF states the COW write-back family is "ALREADY FIXED in-tree" via
`merge_shared_collection_fields`, and instructs lanes to treat "mutation
silently discarded/lost" rows as already-fixed candidates wanting reproduction
rather than patches. That is true **only for the argument boundary**. Rows whose
mutation crosses a return boundary, or whose payload is an enum rather than a
struct, are still live — confirmed by running them, not by inspection. A lane
closing such a row on the strength of that correction will close a live P1.

## What a fix has to do

Merge on the return path as well, with the same value-type discipline (scalars
and nested structs stay value-typed; `Array`/`Dict`/`ByteArray` handles
propagate), and extend the merge to enum payloads so a returned
`Box.Dict(m)`-style variant keeps its live handle. This is a Rust seed change,
so it needs a rebuilt seed; a `.spl`-only edit cannot reach it.

Not attempted in this pass — recorded with reproduction so whoever picks it up
does not re-derive it. `interpreter_call/**` was not on the claimed-path list at
time of writing.

**Revalidated 2026-11-02: still plausible because OPEN, reproduced. Collapses at least two separately-filed rows; no merged fix commit with a passing regression is cited in this doc.**

## Re-verification 2026-11-03 (release/1.0.0 seed, interpreter)

- `test/01_unit/compiler/interpreter/self_field_assign_spec.spl`: 13 examples,
  0 failures (was 11/13). "preserves struct dictionary-field mutations through
  returning free functions" and "preserves self.field mutations passed through
  free functions" now pass; standalone repro (struct `Dict` field written by a
  free fn returning an enum) reads `has("b") == true` after the call.
  The current `merge_shared_collection_fields` (`function_exec.rs:1202`) is
  also handle-identity (`Arc::ptr_eq`) based, O(1) per field.
- NOT fixed, and not fixable by a return-side merge: a `Dict` carried as an
  ENUM payload. `Value::Dict` is `Arc<HashMap>` with copy-on-write
  (`Arc::make_mut`), so a write through a `match` binding forks the map; there
  is no shared handle to merge back into. Even the in-frame case (`Box.Dict(m)`
  then `put(d, k, v)` inside `match`) leaves `m` unchanged on this seed. Fixing
  that needs reference-semantic collection handles (interior mutability) in
  the seed `Value` model -- a design change, tracked by
  `enum_payload_dict_copied_on_function_return_2026-07-28.md`, which stays OPEN.
  The "extend the merge to enum payloads" suggestion above is therefore
  withdrawn: a merge cannot recover a write that was applied to a forked Arc.
- `test/01_unit/lib/common/sdn_coverage_spec.spl` no longer exists in the tree,
  so the second reproduction cannot be re-run.

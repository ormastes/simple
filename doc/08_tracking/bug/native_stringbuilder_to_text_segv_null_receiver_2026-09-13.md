# `StringBuilder.to_text` SEGVs on a null receiver load in native (cranelift, dynload)

- Filed: 2026-09-13
- Found by: `scripts/check/check-native-interp-differential.shs` (first census)
- Census: `doc/10_metrics/infra/native_interp_differential_2026-09-13.md`
- Seed: `build/cargo-f52/release/simple`, sha256 `7b388bd1f570cb14…`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 … native-build --mode dynload --backend cranelift`
- Class: `crash`

## Symptom

`test/01_unit/lib/common/text_advanced_return_types_spec.spl` passes every example
on the seed **interpreter** and SEGVs immediately when the same file is
native-built and run — no examples execute, so the native transcript is empty.

## It is real codegen, not the harness's allowlisted bypass

The harness native-builds spec files with `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1`
**only** when the unresolved set is a subset of five inert process/mmap externs,
and a bypassed binary carries a NULL GOT slot per such name — so a crash must be
triaged to a faulting pc before it can be called a codegen defect. A pc of `0x0`
would be a bypass artifact. This one is not:

```
stop reason = EXC_BAD_ACCESS (code=1, address=0x0)
frame #0: 0x0000000100003f78 …`src__lib__common__string_builder__StringBuilder_dot_to_text + 16
->  0x100003f78 <+16>: ldr    x28, [x8]
    0x100003f7c <+20>: mov    x1, #0x0
    0x100003f80 <+24>: adrp   x8, 3
    0x100003f84 <+28>: add    x8, x8, #0xa0c   ; rt_string_new_literal
```

The faulting pc is **inside generated code** for
`src/lib/common/string_builder.spl`'s `StringBuilder.to_text`, 16 bytes into the
function, loading through a null `x8`. The receiver (or its backing buffer
pointer) is null at entry — the generated prologue dereferences it before any
runtime call. `rt_string_new_literal` is merely the next instruction's target and
is resolved; it is not the failure.

## Relation to already-filed records

Adjacent to but distinct from the 2026-09 native-codegen family. Cite, do not
duplicate:

- `doc/08_tracking/bug/native_optional_unwrap_field_index_by_name_collision_2026-09-12.md` (#742, Optional return-type name loss — this spec is literally a *return types* spec, so a shared root is plausible and worth checking first)
- `doc/08_tracking/bug/unwrap_family_treats_flat_nil_as_present_2026-09-13.md` (#746)
- `doc/08_tracking/bug/stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md` (a different SEGV, MIR-witness route)
- `doc/08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md` (JIT lane, not native)

What is new here is a **named generated function with a reproducible faulting
instruction** in a 5-second build, rather than a whole-stage crash.

## Reproducer

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 \
  build/cargo-f52/release/simple native-build \
  --source src/lib --source test --entry-closure --mode dynload \
  --backend cranelift --threads 1 \
  --entry test/01_unit/lib/common/text_advanced_return_types_spec.spl -o /tmp/a.out
lldb -b -o run -o 'bt 4' -- /tmp/a.out
```

Interpreter control (all green):
`SIMPLE_EXECUTION_MODE=interpreter build/cargo-f52/release/simple run <same spec>`

## Scope limit

Measured on **cranelift** only. Neither seed on this host carries the `llvm`
cargo feature (`--backend llvm` is refused outright), so whether LLVM lowering
shares the defect is untested. **Not fixed here** — F65 owns the seed; this
lane's product is the harness and the census.

## RESOLVED 2026-09-13 — root cause and fix

The SEGV is gone; the spec's six examples all run natively and five of them now
agree with the interpreter (the sixth is a separate, newly-visible defect, filed
as `native_untyped_return_fn_drops_tail_value_2026-09-13.md`).

**The receiver was not "null at entry" in the sense this record guessed — the
call should never have reached `StringBuilder` at all.** Instrumentation
(`SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`, which this branch of codegen did not
previously report on — see below) named it exactly:

```
[CODEGEN-ERASED-RECEIVER-BIND] in 'most_common_char' bare method 'void.len'(0 args)
  receiver_ty=Some(TypeId(0)) bound by name-suffix alone to
  'src__lib__common__string_builder__StringBuilder_dot_len' (1 candidate(s))
```

`if freqs.len() == 0` in `most_common_char` (`src/lib/common/text_advanced.spl`)
has a receiver from an un-annotated function, so its static type is
`TypeId::VOID`. Codegen stringifies the receiver type into the lookup name
regardless, producing **`void.len`** — and every erasure policy in
`codegen/instr/closures_structs.rs` keys on `!lookup_name.contains('.')` to mean
"erased", so a dot-bearing `void.len` read as a genuinely type-qualified call.
Two consequences, both fixed:

1. The bare-builtin route (`bare_builtin_collection`) did not fire, so the call
   was not lowered to the tag-dispatching `rt_len`.
2. The cross-module resolution branch's three unqualified scans were gated only
   on `!enum_helper`, so the first of them bound `len` to the lone linked
   `StringBuilder.len` — which tail-calls `StringBuilder.to_text`, loading field
   0 of a receiver that was never passed. Hence `ldr x28,[x8]` with x8 = 0.
   `rt_string_new_literal` was indeed innocent, as recorded above.

Fix (`codegen/instr/closures_structs.rs`): `strip_erased_receiver_qualifier`
treats a `void.` qualifier as the erasure it is, applied at both policy sites;
and the cross-module scans gain a `no_rebind` predicate covering the builtin
collection idioms alongside the existing enum helpers. The cross-module branch
also now reports its binds through the existing
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND` diagnostic — it never did, which is why this
defect produced zero diagnostic lines while being the whole failure.

**LLVM twin NOT fixed, named rather than hidden:** `mangle.rs`'s bare-`len`
exclusion (~:980) is gated on `!has_type_qualifier`, so `void.len` slips past it
identically. That file is owned by another lane; this record is the citation.

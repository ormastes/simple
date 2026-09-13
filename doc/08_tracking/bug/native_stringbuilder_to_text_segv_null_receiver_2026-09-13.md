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

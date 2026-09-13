# Native: `U32le/U64le .of(v).to_span()` → `.load(sp,0).value()` does not round-trip (U16 does)

- Filed: 2026-09-13
- Found by: `scripts/check/check-native-interp-differential.shs` (first census)
- Census: `doc/10_metrics/infra/native_interp_differential_2026-09-13.md`
- Seed: `build/cargo-f52/release/simple`, sha256 `7b388bd1f570cb14…`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 … native-build --mode dynload --backend cranelift`
- Class: `int-width-bitops`
- Spec: `test/01_unit/lib/common/bytes/ints_spec.spl` (5 of 15 examples diverge)

## Symptom

Interpreter: **15 examples, 0 failures**. Same file, native-built: the *decode*
and the 16-bit *store* examples still pass, while every 32- and 64-bit
**round-trip** fails:

```
Little-endian views
  U16le decodes [0x34,0x12] = 0x1234                       pass
  U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678         pass
  U16le stores 0xBEEF as [0xEF,0xBE]                       pass
  U32le round-trips 0xDEADBEEF                             fail
  U64le round-trips 0x0102030405060708                     fail
5 examples, 2 failures
```

Also failing natively in the same file: `U16be stores 0xBEEF as [0xBE,0xEF]`,
`U64be round-trips 0x0102030405060708 (MSB first)`, and
`LE and BE of the same value produce reversed byte order`.

## What the split tells us

The divergence is **not** in decoding (`load` of a literal byte array is correct
at every width, both endiannesses) and **not** in 16-bit little-endian storing.
It appears when a value is constructed with `.of(v)`, materialised through
`.to_span()`, and read back — and it is width-dependent: `U16le` survives the
store test, `U32le`/`U64le` do not survive the round-trip. That points at the
`of` → `to_span` path (span materialisation / width-sized byte writes) under
native lowering, not at the byte-order logic, which the decode examples exercise
correctly.

`ints_spec.spl:38-42` is the smallest reproducer in the tree:

```simple
it "U32le round-trips 0xDEADBEEF":
    val sp = U32le.of(0xDEADBEEF).to_span()
    expect(U32le.load(sp, 0).value()).to_equal(0xDEADBEEF)
```

## Reproducer

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 \
  build/cargo-f52/release/simple native-build \
  --source src/lib --source test --entry-closure --mode dynload \
  --backend cranelift --threads 1 \
  --entry test/01_unit/lib/common/bytes/ints_spec.spl -o /tmp/a.out && /tmp/a.out
# interpreter control (15/15 green):
SIMPLE_EXECUTION_MODE=interpreter build/cargo-f52/release/simple \
  run test/01_unit/lib/common/bytes/ints_spec.spl
```

## Relation to already-filed records

Not covered by the 2026-09 family: #742/#746/#750/#757 are Optional/`unwrap`
shapes, #765 is dict identity, #771 is `.?` truthiness, and
`result_bound_text_payload_lost_in_stage2_native_codegen_2026-09-13.md` is a text
payload. This is sized-integer span materialisation. The nearest historical
relative is
`doc/08_tracking/bug/native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`
(native byte/slice semantics diverging from the interpreter), which is a
different operation.

## Scope limit

Measured on **cranelift** only — neither seed on this host carries the `llvm`
cargo feature, so LLVM lowering is untested. The spec is correct and stays RED
on the native lane by design: per `.claude/rules/testing.md` a correct spec that
fails is a legitimate artifact and must not be weakened. **Not fixed here** —
F65 owns the seed.

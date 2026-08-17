# Native cross-module arithmetic probe exits 5

## Status

Source-fixed; rebuilt execution pending. Stage2/3 rebuilt successfully from
pre-fetch HEAD `74269ec415`, but the
focused dual-backend gate still stopped before printing
`native-crossmodule-result-u8: pass`. A later mandatory fetch advanced current
source to `448317ea5d`, so those binaries are retained diagnostic evidence, not
current-tip admission artifacts.

## Reproduction

Use the current Stage3 compiler and bootstrap runtime with
`scripts/check/check-native-crossmodule-result-u8.shs`.

Latest retained bounded rebuild evidence (HEAD `74269ec415`):

- Stage2 build log: `build/bootstrap/hir-param-repair/stage2-diagnostic.log`
- Stage3 build log: `build/bootstrap/hir-param-repair/current-tip-stage3-direct.log`
- Stage2 SHA-256: `68520a4fc367af15c5126da3b996141ac176ca42aa188878f1821d94f761b7dc`
- Stage3 SHA-256: `d82ad2d3c7a0a2cd781267cca7f6709752367831dd68f9e982834847fffbad49`
- Stage3 generic admission: version, unsupported `run`, native p2 build, and
  executable output `5` all passed.
- Dual-backend gate: exit `5`; no PASS marker.

Older retained default-LLVM evidence:

- build log: `/tmp/check-native-crossmodule-result-u8-final-2850000/build.log`
- executable: `/tmp/check-native-crossmodule-result-u8-final-2850000/result-u8-default`

The build reports three compiled modules and no failures. Running the binary
returns 5 with empty stdout.

## Boundary

Exit 5 maps to `cross_target_arithmetic_ok()` in
`test/fixtures/native_crossmodule_result_u8/main.spl`. Object inspection and
GDB isolate the bad value to the `high > 0.0` / `0.0 < high` condition: GDB
stops at false-return block `0x40b34d`, and the machine code materializes
`0x8000000000000000u64` as f64 bits `0xc3e0000000000000` (negative 2^63)
instead of positive 2^63.

The textual LLVM backend primes unsignedness from MIR locals, but
`translate_copy_move` overwrote the annotated `u64` destination flag with its
signed literal temporary's flag. Preserving destination-or-source provenance
compiled through fresh Stage2/3 but did not make the final focused gate pass.
Higher review rejected that attempted OR rule because a known signed
destination must not inherit unsignedness. A later destination-preserving
nested guard was correct in source but not in the emitted Stage2/3: disassembly
proved the bootstrap seed resolved both `dest_id` and `src_id` dictionary keys
as `src_id`. The resulting binaries retained the old source-first overwrite.
The cast path itself correctly calls `get_operand_unsigned` and
`value_as_type_signed`; it is not the remaining owner.

## Source fix (2026-07-23)

Copy propagation now uses direct operand-to-ID calls so the bootstrap seed
cannot collapse the two local aliases. An already-primed destination keeps its
authoritative MIR signedness; only an unregistered destination inherits a known
source flag:

```spl
if not self.unsigned_locals.has(self.local_id_value(dest)):
    if self.unsigned_locals.has(self.local_id_value(src)):
        self.unsigned_locals[self.local_id_value(dest)] = self.unsigned_locals[self.local_id_value(src)]
```

The focused source regression rejects the former source-first overwrite. Next,
rebuild Stage2/3 incrementally and run the unchanged cross-module fixture once.
If it still fails, disassemble the keys before considering the separate
`translate_load` provenance audit. Do not weaken or delete the fixture, and do
not advance to Stage4/QEMU until it passes.

## Triage 2026-08-17 — exit code mapped to its exact predicate

Classified against current source, not SHA ancestry.

Exit 5 is now pinned to a specific check. In
`test/fixtures/native_crossmodule_result_u8/main.spl`, `fn main()` returns 5 from
exactly one site: `if not cross_target_arithmetic_ok(): return 5`. So the probe
is not failing generically — `cross_target_arithmetic_ok()` is the failing
predicate, and it is the ONLY thing exit 5 can mean.

That function tests, in order: mixed i64/f64 relational comparison
(`signed_int < 41.5`); u64-vs-i64 comparison across the sign bit
(`high = 0x8000000000000000u64` against `small = 1` for `< <= > >=`); u64-vs-f64
comparison (`high > 0.0`, `high <= 9223372036854775808.0`); u64 division and
modulo (`high / 2u64`, `high % 3u64`); u64 logical shift (`high >> 63u64 == 1u64`);
arithmetic (sign-propagating) right shift by an unsigned count
(`negative >> unsigned_count == -1` where `negative = -2i64`); and
truncation-toward-zero signed division (`-9 / 2 == -4`, `-9 % 2 == -1`).

Every one of those is a mixed-signedness / mixed-width numeric lowering
behaviour, which puts the root cause in the native codegen path, i.e. under
`src/compiler/50.mir/**` or `src/compiler/70.backend/**`. Those trees are CLAIMED
by other lanes in this sweep, so no fix is attempted here. Handing off: bisect
`cross_target_arithmetic_ok()` one predicate at a time — the u64-across-sign-bit
comparisons and the arithmetic-vs-logical shift distinction are the highest-prior
suspects, since both are classic silent-wrong-result lowering bugs.

NOT proven here: the probe was not executed, so it is not confirmed that exit 5
still reproduces today — only that IF it does, this is the predicate at fault.

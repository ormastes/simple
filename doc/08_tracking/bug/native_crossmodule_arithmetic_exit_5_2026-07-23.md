# Native cross-module arithmetic probe exits 5

## Status

Open. Current-source Stage2/3 rebuild successfully, but the focused dual-backend
gate still stops before printing `native-crossmodule-result-u8: pass`.

## Reproduction

Use the current Stage3 compiler and bootstrap runtime with
`scripts/check/check-native-crossmodule-result-u8.shs`.

Current bounded rebuild evidence:

- log: `build/bootstrap/hir-param-repair/current-tip-stage23-fix.log`
- Stage2 SHA-256: `da3a705533a1d6dec92498313bf4408bde2878492a84e68c8a1ff25d46a7e92a`
- Stage3 SHA-256: `518483d2dc313e0cc29e64e54e7df236145314c3e03b9219d8a42b6a2d711b3d`

Older retained default-LLVM evidence:

- build log: `/tmp/check-native-crossmodule-result-u8-final-2850000/build.log`
- executable: `/tmp/check-native-crossmodule-result-u8-final-2850000/result-u8-default`

The build reports three compiled modules and no failures. Running the binary
returns 5 with empty stdout.

## Boundary

Exit 5 maps to `cross_target_arithmetic_ok()` in
`test/fixtures/native_crossmodule_result_u8/main.spl`. Object inspection
isolated the bad value to the `high > 0.0` / `0.0 < high` condition: the
`0x8000000000000000u64` operand was folded as floating-point `-2^63` instead
of `+2^63`.

The textual LLVM backend primes unsignedness from MIR locals, but
`translate_copy_move` overwrote the annotated `u64` destination flag with its
signed literal temporary's flag. Preserving destination-or-source provenance
compiled through fresh Stage2/3 but did not make the final focused gate pass.
Higher review rejected that attempted OR rule because a known signed
destination must not inherit unsignedness. Stage3 disassembly also showed the
two added alias locals collapsing to `src_id`: both reads and the write used
the source key, so the destination flag was never updated.

## Next step

The three-cycle verification cap is exhausted for this session. In a fresh
session, change only copy propagation so an already-primed destination keeps
its authoritative MIR signedness and only a synthetic/unregistered destination
inherits a known source flag:

```spl
if not self.unsigned_locals.has(dest_id):
    if self.unsigned_locals.has(src_id):
        self.unsigned_locals[dest_id] = self.unsigned_locals[src_id]
```

Then rebuild Stage2/3 incrementally and run the unchanged cross-module fixture
once. Do not weaken or delete the fixture, and do not advance to Stage4/QEMU
until it passes.

# Phase 2: the capsule receipt records a pointer-shaped size (NOT `rt_file_size`)

**Filed:** 2026-09-13
**Lane:** phase 2 only (natively compiled pure-Simple Stage 2). Phase 1 (Rust seed) is clean.
**Severity:** blocks Stage 2 admission — every `native-build` unit fails its receipt check.


## CORRECTION 2026-09-13 — this record blamed the wrong function

The title and the analysis below originally attributed the bad size to
`rt_file_size`. **That attribution is wrong**, and the corrected evidence is:

- Receipt line 4 is written from `published.content.len()`
  (`driver_aot_native_output.spl:505`), which compiles to
  `compiler__frontend__core__types__str_len` -> `jmp rt_string_len`. That is
  visible in the phase 2 object's disassembly. It never calls `rt_file_size`.
- The extent guard at `phase_compatibility_path_io.spl:167` passed with the
  same 13-digit value, so the bad number is already present upstream of the
  receipt.
- Five probes built by the seed with phase 2's exact flags — including the
  `impl static fn` shape and cross-module declarations — return CORRECT sizes
  from `rt_file_size`. Both of its implementations return a raw `i64`.

What stands unchanged: the measurement itself (a 691-byte object recorded as
1529351762689), that it is phase-2-only, and that it closes every capsule
receipt. Only the named cause was wrong.

The likely real cause is now the `Dict.remove` lane divergence recorded in
`dict_remove_return_value_differs_native_vs_interpreter_2026-09-13.md`, which
corrupted marker maps in MIR lowering and produced pointer-shaped words in
exactly this way for `str()`. That is a hypothesis, not yet measured here — the
fix for it is landed and a Stage 2 rebuild will settle whether this receipt
defect goes with it.

Side finding while checking: `src/lib/nogc_sync_mut/fs.spl:633` (`-> usize?`)
decodes `size >> 3`, turning 185344 into 23168. A separate latent bug, not
pointer-shaped, and not this one.

## Symptom

Stage 2 builds successfully (`871 compiled, 0 cached, 0 failed`, 105 MB binary),
then fails sanity and is renamed `simple.exe.rejected`. Running that rejected
binary directly on the sanity fixture reproduces the failure:

```
ERROR: 1 unit(s)
  - scripts.check.cert.redeploy_gate.fixtures.hello_world
      reason: native-capsule-receipt-invalid:...:receipt-content-mismatch:expected-bytes=1476:actual-bytes=1476
```

**Equal byte counts on a content mismatch.** That is not a truncation, and the
reason string is built to say so (`driver_aot_native_output.spl:967` reports
lengths precisely so an equal pair localises the fault to content).

## Cause, measured

The receipt is

```
native-capsule-result-v1\n{capsule_identity}\n{object_path}\n{fp.size}\n{fp.content_hash}\n
```

and line 4 — `fp.size` — is garbage:

| | value |
|---|---|
| real object size (`stat -c %s`) | **691** |
| recorded in the receipt | **1529351762689** |

1.5 trillion bytes for a 691-byte object file. The value has the shape of a
millisecond timestamp, not a size. It differs between the write and the verify,
while keeping the same digit count — which is exactly how a *content* mismatch
lands on an *equal* byte count.

`fp.size` comes from `FileFingerprint.from_file`
(`src/compiler/80.driver/driver_build/incremental.spl:623`) via
`incremental_file_size` (`:60`), which is a bare `rt_file_size(path)`.

## Phase 1 control — the same call is correct

```
seed (phase 1), file_size on the same object: 691
stat -c %s on the same object:                691
```

So this is not a runtime bug in `rt_file_size` itself and not a bad path. The
i64 goes wrong only when the call is made from natively compiled Simple.

## What this is NOT

Argument splitting. `rt_file_size` is registered in both codegen tables
(`codegen/llvm/functions/calls.rs`, `codegen/instr/calls.rs`) and its spec is
`(I64, I64) -> I64` — path split into `(ptr, len)`, one `i64` out. That is the
shape the sibling `rt_file_lock` defect had wrong, and it is right here.

The remaining suspects are the i64 return crossing the SFFI boundary in the
native lane, and the struct-field read of `size: i64` at interpolation time.
Both are the same family as the boxing defects filed today
(`jit_some_pattern_payload_shifted_left_3`,
`seed_jit_boxed_int_61bit_drops_high_bits`,
`jit_inline_lambda_text_return_raw_handle`) — a 64-bit payload arriving
un-decoded. Note the garbage here is ODD, so it is not a `<< 3` tag shift.

## Reproduction

```sh
R=.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected
W=build/vtmp/s2probe; mkdir -p "$W/home" "$W/tmp"; cp "$R" "$W/simple.exe"
. ./scripts/setup/windows-msvc-bootstrap-env.shs
HOME="$W/home" TMPDIR="$W/tmp" TMP="$W/tmp" TEMP="$W/tmp" \
  SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
  "$W/simple.exe" native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl \
  --output "$W/hw.exe"
# then compare line 4 of the .capsule-receipt against stat -c %s on the .o
```

Without `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` the run stops earlier, at
`persistent package index admission failed: scv-authority-missing` — a separate
issue with the isolated `stage2_home` the sanity harness creates, which has no
package index and is exactly the cold-init case.

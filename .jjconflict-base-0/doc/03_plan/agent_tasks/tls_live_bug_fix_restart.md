# TLS Live Bug Fix Restart Plan

Date: 2026-04-28
Last revision: 2026-04-28 (post-Phase-5 disproven hypothesis update)

## Current State

Latest verified live result (after compiler `UnitNarrow` patch landed):
- `32 passed, 4 failed`
- Remaining failures:
  - `A2`
  - `D4`
  - `D9`
  - `D10`

## 2026-04-28 Update: Compiler-side hypothesis disproven

The original A2 root-cause hypothesis was **indexed `[u32]` reads lower as
generic signed `I64`, breaking SHA right-shifts in `sha256.spl`**.

That patch landed in Phase 5 of `/dev`:
- `MirInst::UnitNarrow{ from_bits: 64, to_bits, signed, overflow: Wrap }`
  inserted after `MirInst::UnboxInt` for U8/U16/U32/I8/I16/I32 array reads at:
  - [src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:361)
  - [src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:993)
  - [src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs:51)

The patch is **firing as designed**:
- `[narrow-hit-1]` traced 22× on U32 indexed reads.
- `[shr-dispatch]` traced 13× with U32 lhs choosing `ushr` (was `sshr`).

But A2 output is **bit-identical** to pre-patch: `186 247 185 79` (expected
`60 178 ...`). For u32 values that zero-extend to i64 with the top 32 bits
clear, `sshr` and `ushr` produce identical results — so the patch could not
have changed A2 even if it were the right shape.

**Conclusion:** the U32-narrow patch is correct compiler hygiene and stays in
tree, but the actual A2 root cause is elsewhere — almost certainly inside the
pure-Simple SHA-256 / HMAC implementation that A2 is the first to exercise.

## Why A2 is the first pure-Simple SHA call

- `A1` passes through the C-extern fast-path `rt_tls13_hkdf_extract_into` in
  [examples/simple_os/arch/x86_64/boot/baremetal_stubs.c](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/boot/baremetal_stubs.c).
  That extern internally uses a known-good SHA-256 helper. Its passing only
  proves the helper SHA is correct, not the pure-Simple SHA.
- `A2` runs `hkdf_expand_with_info_len(...)` in
  [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl:127).
  That path has **no C-extern fast path**, so it executes pure-Simple
  `hmac_sha256` and pure-Simple `sha256_*` end to end. Therefore A2 is the
  first place in the live test suite that pure-Simple SHA-256 actually runs.
- `A6` passes only because it tests "distinct IKMs no longer collapse in
  extract" — that condition is still satisfied by the helper extract path.

This is consistent with: any pure-Simple SHA bug would surface at A2 first.

## Bisection plan for the new A2 hypothesis

Highest-signal next experiments, ordered cheapest-first:

1. **Pure-Simple SHA-256 RFC vector check (cheap, decisive).**
   - Add a tiny harness in `tls_unit_entry.spl` (or a sibling test entry that
     runs in the same QEMU image) that calls pure-Simple `sha256(empty bytes)`
     and `sha256("abc" bytes)` and prints the first 8 output bytes.
   - Compare against RFC 6234 vectors:
     - `sha256("") = e3b0c442 98fc1c14 9afbf4c8 996fb924 27ae41e4 649b934c a495991b 7852b855` (first byte `0xe3 = 227`).
     - `sha256("abc") = ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad` (first byte `0xba = 186`).
   - If pure-Simple `sha256("abc")` returns `186 ...` correctly, SHA core is
     fine and the bug is upstream in HMAC/HKDF padding.
   - If pure-Simple `sha256("")` is wrong, SHA padding is the bug
     (`sha256_pad_with_len`).

2. **Pure-Simple HMAC-SHA-256 RFC vector check.**
   - Add a harness call to pure-Simple `hmac_sha256` for RFC 4231 TC1
     (key=20 × 0x0b, data="Hi There") and compare first 8 output bytes against
     the RFC `b0344c61 d8db3853 ...` (first byte `0xb0 = 176`).
   - If SHA passed step 1 but HMAC fails here, the bug is in HMAC pad
     construction (ipad/opad XOR or key-block fill in
     [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl)).

3. **Byte-pack chain check.**
   - If steps 1+2 both pass, the bug is in the byte-to-word packing
     (`_u8_at`, `.to_u32()`, big-endian word assembly) on the way *into* SHA.
   - Read [src/os/crypto/sha256.spl](/home/ormastes/dev/pub/simple/src/os/crypto/sha256.spl)
     around the input-block assembly and check whether multi-byte reads
     respect MSB-first big-endian ordering for the schedule.

4. **HKDF-Expand framing.**
   - Last fallback. If 1+2+3 are clean, the failure is in
     `hkdf_expand_with_info_len`'s T-block chaining (counter byte placement,
     info concatenation, or T(0) handling) in
     [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl:127).
   - But the plan's earlier review said this layer looks RFC-correct, so
     deprioritize until the lower three are cleared.

The `186 247 185 79` first bytes are striking because **`186 = 0xba`** is the
exact first byte of `sha256("abc")`. That coincidence suggests A2 may be
inadvertently SHA-hashing the literal bytes of `"abc"` (or some constant
test/string fixture) instead of the HKDF-Expand prefix it should be hashing.
Treat that as a strong lead for step 2/3.

## Highest-signal code locations for the new hypothesis

- Pure-Simple SHA core: [src/os/crypto/sha256.spl](/home/ormastes/dev/pub/simple/src/os/crypto/sha256.spl)
  - SHA padding `sha256_pad_with_len`
  - Schedule construction `w[0..16]` byte-pack
  - Round loop, including `small_sigma0/1`, `big_sigma0/1`
- HMAC + HKDF: [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl)
  - `hmac_sha256` ipad/opad construction
  - `hkdf_expand_with_info_len` T-block chaining
- TLS unit entry harness: [examples/simple_os/arch/x86_64/tls_unit_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/tls_unit_entry.spl)
  - Where the bisection harness needs to be inserted (and removed in ship phase)

## What stays in tree regardless of next phase

The compiler `UnitNarrow` patch from Phase 5 is kept. Reasons:
- It is empirically correct hygiene (pre-patch `sshr` for u32 was wrong even if
  this particular A2 input did not exercise it).
- Reverting it would re-introduce a latent unsigned-correctness gap in any
  future pure-Simple cryptographic code that does shift bit-31-set values.

The diagnostic prints in `tls_unit_entry.spl` (A2 `okm_a` prefix; D4/D9/D10
content type and length) are still required until AC-5 (live gate green) is
met.

## 2026-04-28 Update 2: Bisection results — SHA round loop is wrong, AND `.to_u64()` reads inconsistently

After R1's `UnitNarrow` patch landed, bisection of the bare-metal compiled
build of pure-Simple SHA-256 against RFC 6234 vectors revealed:

### `sha256("")` produced output (32 bytes)

Got vs RFC expected:
```
[ 0..7 ]: 227 22 196 66 19 252 28 20      vs  227 176 196 66 152 252 28 20
[ 8..15]: 154 251 244 25 153 111 185 36   vs  154 251 244 200 153 111 185 36
[16..23]: 39 174 65 228 100 155 147 76    vs  39 174 65 228 100 155 147 76
[24..31]: 164 149 153 27 15 82 23 85      vs  164 149 153 27 120 82 184 85
```

5 of 32 bytes wrong: positions 1, 4, 11, 28, 30. **Every wrong byte equals the
correct byte right-shifted by 3:**
- got[1]=0x16 = 0xb0>>3 (correct=0xb0)
- got[4]=0x13 = 0x98>>3 (correct=0x98)
- got[11]=0x19 = 0xc8>>3 (correct=0xc8)
- got[28]=0x0f = 0x78>>3 (correct=0x78)
- got[30]=0x17 = 0xb8>>3 (correct=0xb8)

A stuck `>> 3` is being applied at specific points inside SHA's round mixing.
Since `small_sigma0(w) = ROTR^7(w) ^ ROTR^18(w) ^ (w >> 3)`, the raw `>> 3`
operation appears once in `small_sigma0` and propagates through 48 schedule
rounds plus 64 round operations. A miscompilation of that single `>> 3` could
corrupt specific output bytes via the round-mixing structure, but exactly
which 5 bytes is hard to predict from first principles.

### Bonus finding: `.to_u64()` reads inconsistently with shift-extraction

Three adjacent reads of the same `h[0]: u32` produce two different values:
- `h[0].to_u64()` (string-interpolation form): `3820012610 = 0xe3befc02`
- `val w0 = h[0]; ((w0 >> 24) & 0xFF, ...)`: `0xe316c442` (bytes 227 22 196 66)
- `(h[0] >> 24) & 0xFF, (h[0] >> 16) & 0xFF, ...` (inline literal): `0xe316c442`

The shift-extraction reads are consistent (both = 0xe316c442). The
`.to_u64()` interpolation reads yet a third value (0xe3befc02). This is a
second, separate codegen bug — independent of the round-loop problem above —
but it confounds debugging because BISECT prints using `.to_u64()` show
different bits than the byte serialization actually uses.

### Where the bug is NOT

- HKDF framing: the `hkdf_expand_with_info_len` body in
  [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl:127)
  is RFC-correct and not exercised before SHA fails.
- HMAC pad construction: the HMAC-TC1 RFC vector also fails, but only because
  it depends on SHA. Once SHA core is right, HMAC will follow.
- Byte-pack into `[u32] w` in `sha256_process_block`: input block bytes for
  `sha256("")` are `0x80 || 0x00... || 0x00 (length=0)`, which produces
  `w[0] = 0x80000000, w[1..16] = 0`. If byte-pack were wrong, the entire
  output would be scrambled, not just 5 of 32 bytes.

### Where the bug IS (open hypotheses)

- **H1**: miscompilation of `(w >> 3)` inside `small_sigma0` itself — produces
  the wrong schedule recurrence for some `w[t]` values.
- **H2**: miscompilation of variable rotation (`hh = g; g = f; ...; b = a;
  a = ...`) at the end of each round — Cranelift SSA construction may have an
  ordering or aliasing bug for back-to-back `var` writes that the R1 patch
  doesn't address.
- **H3**: miscompilation of additive accumulation `_u32_mask(h[i] + a)` in the
  final state-emission loop — same `[u32]` array indexed read inconsistency
  observed above could cause one operand to be read with extra `>> 3` while
  the other is correct.

Decisive next probes (each one rebuild + QEMU run):
- Replace `var`-rotation in the round loop with explicit fresh `val`s assigned
  back at the end. If empty SHA flips correct, H2 is right.
- Print `w[16]` (must be 0x80000000 for empty input) after schedule expansion.
  If wrong, H1 is right.
- Print `(a, b, c, d, e, f, g, hh)` immediately before the final state-emit.
  If they match RFC SHA-256 round-63 trace for empty input but final h[] is
  still wrong, H3 is right.

## Scope reassessment

The original `/dev` task scope was "fix A2/D4/D9/D10 in the live TLS gate."
Bisection has shown the actual root cause is deeper: pure-Simple SHA-256 in
compile-mode (Cranelift bare-metal build) is broken on every input we tested.
This is now a **compiler/codegen bug fix**, not a TLS-side fix. Three viable
paths:

1. Continue inline debugging with `var`→`val` rewrite or further bisection
   probes. Each iteration is one ~12 second rebuild + QEMU run. May take many
   rounds.
2. Workaround: add an `rt_tls13_hkdf_expand_into(...)` C extern fast-path that
   mirrors the existing `rt_tls13_hkdf_extract_into` used by A1, so HKDF-Expand
   doesn't go through pure-Simple SHA at all. Closes the TLS gate cleanly but
   does not fix the underlying compiler bug. Document the compiler bug as a
   separate `/bug` track.
3. Pause this `/dev` session, document the compiler bug as its own
   investigation, ship the R1 `UnitNarrow` patch (correct hygiene that stays),
   and tackle the SHA codegen bug in a fresh `/dev` session with a different
   approach.

Primary live command:

```bash
SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl --system --sequential --fail-fast
```

Direct serial command:

```bash
timeout 60 qemu-system-x86_64 -no-user-config -monitor none -net none -machine q35 -cpu qemu64 -m 2G -serial stdio -display none -no-reboot -kernel build/os/simpleos_tls_unit_x86_64.elf -vga std -device isa-debug-exit,iobase=0xf4,iosize=0x04 2>&1 | tr -d '\000'
```

## Important Current Evidence

### A2

Current live debug:
- `A2 okm_a: 186 247 185 79`
- expected first bytes: `60 178`

What is already known:
- `A1` passes, so `HKDF-Extract` / PRK generation is correct enough for RFC TC1.
- `A6` passes, so distinct IKM values no longer collapse in extract.
- `hkdf_expand_with_info_len()` structure in [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl:127) looks RFC-correct.

Strongest current hypothesis:
- Pure SHA/HMAC is still broken on `[u32]` array reads.
- The most likely choke point is indexed integer-array lowering in [src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:346).
- Current reasoning:
  - `[u32]` reads in [src/os/crypto/sha256.spl](/home/ormastes/dev/pub/simple/src/os/crypto/sha256.spl:220) lower through `rt_index_get(...)` plus `UnboxInt`.
  - the compiler then effectively retypes those results as generic signed `I64`
  - that is a bad fit for SHA schedule/state arrays `w[...]` and `h[...]`

Highest-signal code locations:
- [src/os/crypto/sha256.spl](/home/ormastes/dev/pub/simple/src/os/crypto/sha256.spl:220)
- [src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:346)
- [src/compiler_rust/compiler/src/codegen/instr/body.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/codegen/instr/body.rs:145)
- [src/compiler_rust/compiler/src/codegen/instr/mod.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/codegen/instr/mod.rs:1122)
- [src/compiler_rust/compiler/src/codegen/instr/core.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/codegen/instr/core.rs:152)

### D4 / D9 / D10

Current live debug:
- `D4`: decrypt returns `ct4=0`, `dt4.len()=5`
- `D9`: decrypt returns `ct9=0`, `dt9.len()=0`
- `D10`: decrypt returns `ct10=0`, `dt10.len()=5`

What is already known:
- `D3` passes.
- `D3` currently uses helper encrypt + helper decrypt.
- `D4`, `D9`, `D10` currently use pure Simple encrypt + helper decrypt.
- `record13_decrypt()` currently prefers helper decrypt first in [src/os/tls13/record13.spl](/home/ormastes/dev/pub/simple/src/os/tls13/record13.spl:248).

Strongest current hypothesis:
- Remaining record failures are a mixed-path interoperability bug.
- The helper decrypt path authenticates the record but the recovered inner plaintext behaves as if the final content-type byte is `0x00`.
- This does not look like generic header parsing failure.

Highest-signal code locations:
- [src/os/tls13/record13.spl](/home/ormastes/dev/pub/simple/src/os/tls13/record13.spl:148)
- [src/os/tls13/record13.spl](/home/ormastes/dev/pub/simple/src/os/tls13/record13.spl:248)
- [src/os/crypto/aes128_gcm.spl](/home/ormastes/dev/pub/simple/src/os/crypto/aes128_gcm.spl:508)
- [examples/simple_os/arch/x86_64/boot/baremetal_stubs.c](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:10832)

## Changes Already In Place

Do not accidentally revert these without re-evaluating live TLS:

### Compiler / lowering

- Typed literals now lower correctly in:
  - [src/compiler_rust/compiler/src/hir/lower/expr/mod.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/hir/lower/expr/mod.rs)
  - [src/compiler_rust/compiler/src/hir/lower/expr/literals.rs](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/hir/lower/expr/literals.rs)

### TLS byte-path hardening

- Indexed byte reads replaced fragile iteration in:
  - [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl)
  - [src/os/tls13/transcript.spl](/home/ormastes/dev/pub/simple/src/os/tls13/transcript.spl)
  - [examples/simple_os/arch/x86_64/tls_unit_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/tls_unit_entry.spl)

### Record helper adjustments

- Record helper nonce XOR fix is already present in:
  - [examples/simple_os/arch/x86_64/boot/baremetal_stubs.c](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/boot/baremetal_stubs.c)

- Current record-path compromise is already present in:
  - [src/os/tls13/record13.spl](/home/ormastes/dev/pub/simple/src/os/tls13/record13.spl)
  - helper encrypt is used only for the known-good `D3` case
  - helper decrypt is still preferred first

## Recommended Restart Order (revised 2026-04-28)

### 1. Bisect pure-Simple SHA / HMAC / byte-pack first

Reason:
- The compiler-side hypothesis was disproven empirically: the `UnitNarrow`
  patch fires correctly but A2 output is bit-identical, so `>>` dispatch is
  not the cause.
- A2 is the first call in the live suite to exercise pure-Simple SHA. Any
  pure-Simple SHA / HMAC / byte-pack bug surfaces here first.
- The first byte of A2 output (`186 = 0xba`) matches `sha256("abc")[0]`,
  suggesting the test fixture or harness may be hashing the wrong input.

Implementation order: see "Bisection plan for the new A2 hypothesis" above.
Cheapest first: SHA RFC vectors → HMAC RFC vectors → byte-pack → HKDF-Expand
framing. Stop at the first failing layer.

Suggested validation after each bisection step:

```bash
cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver
SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl --system --sequential --fail-fast
```

Success condition:
- `A2` passes (RFC TC1 first bytes `60 178 ...`)

### 2. Re-evaluate D after A2

Reason:
- `D` is already narrowed, but the current mixed-path behavior is harder to reason about than `A2`
- reducing remaining unknowns first is better than stacking more record-path workarounds

Expected outcome possibilities:
- `D4/D9/D10` still fail unchanged
- `D` shifts shape once compiler numeric representation is corrected

### 3. If D still fails, isolate mixed-path interop explicitly

Most useful next experiment:
- temporarily force both record directions onto the same implementation family for the failing cases
- compare:
  - pure encrypt + pure decrypt
  - helper encrypt + helper decrypt
  - pure encrypt + helper decrypt

Goal:
- determine whether the remaining bug is:
  - pure encrypt output contract
  - helper decrypt returned-inner contract
  - or `record13_decrypt()` consumption of helper-returned bytes

## Diagnostic Notes To Preserve

Current TLS harness diagnostics in [examples/simple_os/arch/x86_64/tls_unit_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/tls_unit_entry.spl) are useful and should be kept until the live lane is green:
- `A2` prints `okm_a` prefix
- `D4`, `D9`, `D10` print returned content type and data length

Do not remove them until the remaining 4 live failures are resolved.

## Things That Look Less Likely Now

- HKDF framing bug in [src/os/tls13/hkdf.spl](/home/ormastes/dev/pub/simple/src/os/tls13/hkdf.spl)
- transcript framing/hash bug
- generic TLS header/tag-split bug in [src/os/tls13/record13.spl](/home/ormastes/dev/pub/simple/src/os/tls13/record13.spl)
- `_tls_copy_runtime_bytes()` or `_tls_runtime_array_from_bytes()` as the primary cause of `D4/D9/D10`

## Exit Criteria

Minimum target before broader regression:
- live TLS unit gate fully green

```bash
SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLEOS_QEMU_TLS_LIVE=1 bin/simple test test/system/os_tls_spec.spl --system --sequential --fail-fast
```

Then run:

```bash
bin/simple test test/system/os_tls_system_spec.spl
bin/simple test test/system/os_tls_client_auth_spec.spl
bin/simple test test/system/os_tls_hosted_interop_basic_spec.spl
bin/simple test test/system/os_tls_hosted_interop_mtls_spec.spl
bin/simple build check
```

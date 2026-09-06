# sha256_core value-tagging defect silently corrupts live SHA-256 digests

**Status:** FIXED (`.spl`-level workaround) 2026-08-11, this session — see
*2026-08-11 second follow-up: root cause isolated and fixed* below. Both FIPS
"empty" and "abc" vectors now pass via `sha256_bytes_scalar`, and the full
`sha256_simd_parity_spec` (10 checks incl. multi-block, 1024/2048-byte
payloads) passes. Root cause was the untyped `list` return/param type in
`sha256_core.spl` — switching every `list` annotation (return types, params,
and internal `var`/`val` declarations) in that file to `[i64]` eliminates the
corruption.
**Found:** 2026-08-11
**Severity:** was HIGH — `sha256_bytes_scalar` is live code and produced wrong digests

## 2026-08-11 second follow-up — root cause isolated and fixed

**Exact corrupting call boundary, isolated with a minimal probe (not the full
pipeline).** The trigger is not any specific one of the ~10 nested calls
inside `sha256_process_block` — it is the **untyped `list` annotation** used
throughout `sha256_core.spl` for every list-typed return/param/local. Minimal
repro (ran directly with `bin/simple <file>.spl`, no timeout, seconds not
minutes):

```
val untyped: list = [0x6a09e667, 0xbb67ae85]
val u0 = untyped.get(0)
print "{u0 + 5}"        # prints "<value:0x6a09e66c>" -- NOT decoded to int
                          # 0x6a09e66c IS the correct decimal answer
                          # (1779033708) printed as a hex/pointer-looking tag

val typed: [i64] = [0x6a09e667, 0xbb67ae85]
val t0 = typed.get(0)
print "{t0 + 5}"        # prints "1779033708" -- correct, decoded
```

**Value type at the corrupting boundary:** a scalar `i64` returned by
`list.get()` where the list's static type is the untyped `list` (not
`[i64]`). The element is boxed/tagged; `print` on the bare boxed value alone
has a special-cased decode path and shows the right number, but arithmetic on
it (`+`, `<<`, or passing it to another function as an `i64`-typed arg)
operates on the raw tagged representation instead of the decoded int. That
explains the earlier observation that the corruption factor flips direction
(×8 vs ÷8) and compounds with call depth: at each additional hop the tag
bits get reinterpreted differently depending on how the value is consumed.
This matches the documented **container-boxing / value-tagging family**
(`reference_native_dict_get_struct_corrupt_len_minus_one`,
`reference_list_get_returns_value_shifted_left_3`) — `list.get()` on an
untyped `list` does not fully decode its element for downstream arithmetic,
only for direct `print`.

**Fix applied:** in `src/lib/common/crypto/sha256_core.spl`, changed every
`list` type annotation to `[i64]` — function return types
(`sha256_k_constants`, `sha256_initial_hash`, `sha256_core_compress_block`,
`create_sha256_context`, `sha256_pad_message`, `sha256_process_block`),
function params (`h`, `block`, `bytes`), and internal `var`/`val`
declarations (`padded`, `w`, `new_h`, `data`). The prior investigation's note
that "typing the signatures `list` -> `[i64]` does not fix it" only re-typed
function signatures, not the internal `var w = []` / `var padded = []` /
`var new_h = []` locals inside the same functions — those untyped locals
were still boxing their elements even with a typed signature around them,
which is why that earlier attempt didn't work.

**A second, independent bug was uncovered and fixed while verifying:** a
dead/unused helper `fn compress_block(a: i64, ... w: i64) -> (i64, i64)` in
`src/lib/common/crypto/sha256.spl` (never called anywhere in the repo —
confirmed by grep, excluding vendored JS/Rust zlib code that defines an
unrelated same-named symbol) was cross-module name-colliding with the
compiler's crypto-intrinsic pattern-matching engine's internal name for
`sha256_core_compress_block` (see the file's own "Pattern-Matchable
Wrappers" section). The compiler emitted
`compiler_cross_module_private_symbol_collision`, non-deterministically
falling back to the wrong definition depending on what else was compiled
into the same run — this alone was enough to make `sha256_bytes_scalar`
produce wrong digests even after the `[i64]` retyping fix above, when
invoked from certain call sites/paths. Deleted the dead `compress_block`
function entirely (code-style: delete unused code, don't rename around it).

**Verification, both fixes applied:**
- `sha256_bytes_scalar([])` (empty) == `e3b0c442...b855` — PASS
- `sha256_bytes_scalar([97,98,99])` ("abc") == `ba7816bf...5ad` — PASS
- `test/01_unit/lib/common/crypto/sha256_simd_parity_spec.spl`, run directly
  with `bin/simple <file>.spl`: all 10 checks PASS (canonical "abc", 1-byte,
  55/56/64-byte boundary cases, 1024- and 2048-byte multi-block payloads,
  native-byte path incl. beyond 64 KiB) — no `compress_block` collision
  warning printed.

**Why the earlier 60s timeout happened, and why it does not indicate a hang:**
`bin/simple <file>.spl` run directly completes in a few seconds and prints
all correct output. Running the spec directly also completes and prints all
10 `✓` PASS lines well within the wall clock — but the *process* does not
exit afterward; something after the last assertion (teardown/GC/daemon
handoff, not measured further this session) keeps it alive until the shell's
`timeout` kills it (`EXIT=124`). This is a separate, orthogonal harness
issue: the checks themselves run and pass fast; only process exit hangs.
Read the printed `✓`/`✗` lines, not the exit code, when this file is
invoked directly.

**Not investigated further this session:** whether the `compress_block`
collision class recurs elsewhere in the crypto module family (`sha1.spl`,
`hmac.spl`, `sha384`/`sha512`) — this session only found and fixed the one
instance blocking SHA-256.

**Regression specs:** per this doc's own specs-last discipline, no new specs
were added — the existing `sha256_simd_parity_spec.spl` already asserts real
FIPS vectors, was previously failing/unobserved due to the two bugs above,
and now passes; it stands as the regression gate for this fix.

## 2026-08-11 follow-up — root cause narrowed further, no working fix found this session

**Re-confirmed the defect is real and still reproduces exactly as filed**,
using `bin/simple run` (Rust-seed Cranelift JIT, the default/live lane) against
FIPS "abc": `sha256_bytes_scalar([97,98,99])` still does not match
`ba7816bf...`. `runtime_native.c` compiling clean (confirmed still true this
session, `a1f3adeff791`) did not change anything here — that fix is orthogonal.

**Narrowed the trigger below the module-return theory.** A direct,
non-cross-module test proves plain integer literals are unaffected:
```
val b0 = 97
print "{b0 << 24}"     # 1627389952 -- CORRECT
```
But the same literal value, after passing through `padded.get(idx)` where
`padded` is a `list` **returned from a different function/module**
(`sha256_pad_message` in `sha256_core.spl`, called from `sha256.spl`), then
used in `<<` arithmetic, is wrong:
```
val b0 = padded.get(0)     # displays 97 -- looks correct!
print "{b0 << 24}"          # 203423744, i.e. 97 << 21 (not 97 << 24) -- WRONG
```
Critically, **`print "{b0}"` alone shows the correct value `97`** — the
corruption is invisible to a plain read/print/equality check and only
surfaces once the value participates in further bitwise arithmetic. This is
why `sha256_pad_message([97,98,99])` "returning `776,784,792,1024`" (the
original filing's repro) undersells the shape: printing the returned list
directly can look CORRECT (`97,98,99,128`) while the *same* elements are
wrong by a factor when later shifted — the visible defect depends on how the
value is consumed downstream, not just on the return itself.

**Tried and refuted: reboxing (copy the list into a fresh local list via a
`while` + `.push()`/`.get()` loop) fixes the isolated 4-line repro above, but
does NOT fix the full pipeline.** Confirmed empirically:
- Rebox `padded` and `h` immediately after receiving them from
  `sha256_pad_message`/`sha256_initial_hash` in `sha256_bytes_scalar`: no
  change to the final digest.
- ALSO rebox `sha256_process_block`'s own `h`/`block` PARAMETERS on entry
  (not just its return value) inside `sha256_core.spl`: still no change to
  the final digest.
- A minimal test isolated from `sha256.spl` entirely (new `sha256_via_core`
  wrapper calling only `sha256_pad_message`/`sha256_initial_hash`/
  `sha256_process_block` with the same reboxing) still does not match FIPS
  vectors, though the specific wrong digest changes between runs/edits —
  consistent with the corruption depending on the exact shape/depth of the
  call chain, not a single fixed offset.
- A same-module wrapper function (an in-file helper that just does
  `xs.get(0)` on a parameter) *also* corrupts a value passed as an argument,
  independently of any `return` — e.g. wrapping a correct `padded.get(0)`
  read in one extra function call produced a value 8x TOO LARGE (the
  opposite direction from the too-small case above). **This means the defect
  is not one fixed `<<3` shift with one fixed direction — it can appear as
  `<<3` (÷8) after a return and as `>>3`-inverse (×8) after a parameter pass,
  and can compound across multiple hops.** Reboxing at any single hop does
  not neutralize corruption introduced at a different hop deeper in the same
  call chain (`sha256_process_block` internally calls
  `add_mod32`/`rotr32`/`shr32`/`sha256_ch`/`sha256_maj`/`sha256_sigma0`/
  `sha256_sigma1`/`sha256_little_sigma0`/`sha256_little_sigma1`, each itself
  a function call, several crossing into a THIRD module,
  `std.common.crypto.types` — any of these can be a corruption point, and
  this session did not isolate which specific one(s)).

**Given this, no `.spl`-level workaround was completed in the time
available.** Reboxing every argument at every one of these ~10 call sites
inside the 64-round loop was not attempted (would need call-site-by-call-site
verification, likely with a performance cost from the extra copies, and there
is no guarantee reboxing generalizes the same way at every hop given the
direction-flip observed above). **Speculative edits to `sha256.spl` /
`sha256_core.spl` made while investigating this were reverted before
finishing this session — the working tree for both files is unchanged from
before this investigation.** No FIPS regression specs were added (correctly,
per this doc's own existing guidance — they would be permanently RED).

**Next investigator: start from the isolated 4-line repro above** (literal
`<<` correct, `list.get()`-from-cross-module-return `<<` wrong by an exact
power-of-two factor that flips sign depending on return-vs-argument
direction and compounds with call depth). That is a much smaller, more
tractable repro than the full SHA-256 pipeline, and should be pursued as a
compiler/runtime defect (tag-box decode/encode at function
call/return boundaries in the JIT lane), not chased further inside
`sha256_core.spl`.

## `sha256_simd_parity_spec` — located, DOES assert real FIPS vectors; run result inconclusive this session

Found: `test/01_unit/lib/common/crypto/sha256_simd_parity_spec.spl`. It is NOT
a weak/no-op spec — its first `it` block asserts the exact canonical "abc"
digest (`ba7816bf...`) against BOTH `sha256_bytes` and `sha256_bytes_scalar`
via `bytes_to_hex(...).to_equal(expected)`, plus several SIMD-vs-scalar parity
checks at block-boundary sizes. Its own header comment already flags the
likely explanation: **"`bin/simple test` is the false-green path"** — it
explicitly instructs running it via direct invocation (`bin/simple <file>`)
instead. Also note it imports from `std.crypto.sha256`/`std.crypto.types`,
NOT `std.common.crypto.sha256`/`std.common.crypto.crypto.types` — worth
checking whether `std.crypto.*` is a re-export or a genuinely different
module before assuming it exercises the exact code path this doc is about.

**Not resolved this session:** both `bin/simple test/01_unit/.../sha256_simd_parity_spec.spl`
(direct invocation, as the file recommends) and `bin/simple test test/01_unit/.../sha256_simd_parity_spec.spl`
(the `test` subcommand) were killed by a 60s timeout in this session without
producing a verdict line either way. This is itself worth recording: a spec
that cannot even be observed to finish in 60s is not something CI's normal
green/red gate can be trusted to have exercised meaningfully either, unless
CI uses a materially longer timeout than was tried here. Next investigator:
re-run with a longer timeout (or `run_in_background`) and read the actual
PASS/FAIL output before concluding anything about why this spec did or didn't
catch the digest corruption.

## Summary

`src/lib/common/crypto/sha256_core.spl` returns **corrupted values** across the
module boundary. Elements come back multiplied by 8 (shift-left-3), so every
digest computed through it is wrong.

FIPS 180-4 vectors, run for real:

| Path | empty | `"abc"` | 448-bit |
|------|-------|---------|---------|
| live `sha256_text` | PASS | PASS | — |
| via `sha256_core` | **FAIL** | **FAIL** | **FAIL** |

## The corruption

`sha256_pad_message([97, 98, 99])` returns `776, 784, 792, 1024` for inputs
`97, 98, 99, 128` — each exactly ×8.

Critically, **`128` is a literal** (`0x80`) pushed *inside* the function, so this
is not input marshalling. The values are corrupted on the way out.

## The algorithm itself is correct

Ruled out by differential testing against the FIPS-passing live implementation:
round constants (`k[0]`, `k[8]`, `k[63]`), the initial IV, `ch`, `maj`, all four
sigma functions, and the padding length all agree. A renamed byte-identical copy
produces identical wrong output, so no crypto-intrinsic substitution is involved.

This is the documented shift-left-3 / container-boxing family. Minimal `list`
push/get and plain cross-module list returns are both CLEAN, so the trigger is
narrower than "cross-module list" — that narrowing is the useful lead.

Typing the signatures `list` -> `[i64]` does **not** fix it (tried and reverted).

## Why it matters

`src/lib/common/crypto/sha256.spl:381 sha256_bytes_scalar` is **live code** and
the declared parity target for `sha256_simd_parity_spec`. It routes through
`sha256_process_block` and is therefore silently producing wrong digests.

**That parity spec is either not running or not asserting vectors** — otherwise
this would already be red. Determining which is part of the fix.

## Corrected premise (recorded so it is not rediscovered)

This module was initially reported as "structurally un-importable" because it has
**0 `pub fn` and 14 bare `fn`**. That inference is WRONG. `pub` is not the export
form in `src/lib/common/**`:

- `sha256_core.spl` is imported by `sha256.spl:5` and `sha256_simd.spl:11`
- `sha1.spl` — 0 `pub`, 33 bare `fn`, imported by 4 files
- `hmac.spl` — 0 `pub`, 16 bare `fn`, imported by 8 files
- `pub fn` appears only under `nogc_sync_mut/`

`pub` marks non-filename-matching items (see `test/fixtures/visibility_test/`);
it is not required for cross-module import. Proven by execution: a probe
importing `sha256_initial_hash` / `sha256_pad_message` / `sha256_process_block`
across the module boundary ran and returned values.

## Family enumeration

Enumerated by round constant `0x428a2f98`, not by filename — 941 files merely
*mention* sha256; only these carry a real implementation.

Owned: `src/lib/common/crypto/{sha256_core,sha256,sha256_simd}.spl`,
`src/os/crypto/{sha256,sha384,sha512,jwt,cose}.spl`,
`src/lib/common/jwt/sign.spl`, `src/lib/nogc_sync_mut/src/exp/config.spl`,
`src/runtime/runtime_native.c`,
`examples/09_embedded/.../{tls13_sha256_helper.c,crypto_common.h}`.
Vendored (excluded): `ring`, `sha2`, `lzma-sys`, `compiler_builtins`.

## Next steps, in order

1. Narrow the tagging trigger from the `776/784/792/1024` repro.
2. Fix `sha256_bytes_scalar` so the live path produces correct digests.
3. **Then** add FIPS vector specs as the regression gate — adding them first
   would land a permanently RED spec against an engine defect.
4. Determine why `sha256_simd_parity_spec` did not catch this.

## Blockers

No pure-Simple compile path currently exists to verify an engine fix:
`runtime_native.c` does not compile
(`runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md`),
`bootstrap/stage3/simple native-build` SIGSEGVs, and `bin/simple` is the Rust seed.

# Vulkan font lane: whole-atlas SHA-256 costs ~10 min per atlas upload

- **Filed:** 2026-08-04
- **Status:** FIXED (this change)
- **Site:** `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl` (was line 360)
- **Impact:** every spec touching vector-font rendering on the vulkan lane was
  effectively unverifiable; it dominated two separate investigation lanes.

## Symptom

A two-glyph draw on the vulkan font lane burned tens of minutes of CPU. The
cost showed up as `evidence_overhead_ns`, not as render time.

## Root cause

```
self.font_atlas_payload_sha256 = sha256_u8_hex(atlas_payload)
```

The font atlas is a **fixed 1024x1024** — `FONT_ATLAS_WIDTH` /
`FONT_ATLAS_HEIGHT` in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:464-465`
— regardless of how many glyphs the batch actually draws. So even a two-glyph
draw hashed `1024 * 1024 * 4 = 4,194,304` bytes.

The vulkan font lane runs **interpreted**: the `vulkan_sffi_*` externs are
unresolved in the JIT, and an unresolved external symbol drops the *whole
module* to the interpreter (`[jit-fallback] ... whole module dropped to the
interpreter`). Interpreted `sha256_u8_hex` measures **~7.2 KB/s**.

This is the same class of defect already documented for font *asset* loading in
`src/lib/common/encoding/font_registry.spl:566-575` and
`doc/08_tracking/bug/engine2d_load_font_interpreter_3kb_per_sec_2026-07-25.md`.
It is not an inefficiency in the SHA-256 code — 64-byte blocks of interpreted
bit-twiddling simply cost ~23 ms each.

Note the call was already correctly gated behind the atlas dirty check
(`font_atlas_generation` / `font_atlas_owner_identity`), so it ran once per
atlas mutation, not once per quad. The problem is that the *cold* cost alone is
~10 minutes, and every fresh render pays it once.

## Measurements (external, `/usr/bin/time`; never in-language)

Interpreted (`SIMPLE_EXECUTION_MODE=interpret`), replicating the exact hot path
(1024x1024 `[u32]` atlas -> `_vulkan_font_pixels_to_bytes` -> digest):

| step | wall |
|---|---|
| convert only (4 MB) — unavoidable, feeds the upload | **11.36 s** |
| convert + old whole-atlas `sha256_u8_hex` | **635.85 s** |
| => old hash step alone | **624.5 s** (98.2% of the path) |
| convert + new digest | **~14.8 s** |
| => new digest step alone | **~3.4 s** |

Primitive rate check confirming linearity of the old path: 16 KB = 2.29 s,
32 KB = 4.26 s => ~7.2 KB/s; extrapolating to 4,194,304 B predicts ~580 s,
consistent with the measured 624.5 s.

**Atlas-upload path: 635.85 s -> ~14.8 s (~43x). Digest step: ~180x.**

## What the token actually guarantees

Audited across every consumer in `src/`, `test/`, `scripts/` and `doc/` before
changing anything. It is a **change-detection token with a well-formedness
gate** — *not* a cryptographic or parity checksum:

- **Shape:** `vulkan_font_stage_evidence_ready` requires `.len() == 64`
  (`backend_vulkan_font.spl`); the live-evidence checker requires 64 lowercase
  hex chars (`scripts/check/check-macos-gpu-2d-live-evidence.shs` `sha256_valid`,
  `test/02_integration/rendering/macos_gpu_2d_live_harness.spl:120`).
- **Change detection:** the only value comparisons are warm-vs-cold equality
  *within one receipt* (`macos_gpu_2d_live_harness.spl:500`,
  `check-macos-gpu-2d-live-evidence.shs:875-876`) and stability across samples
  (`test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl:490,494`).
- **NOT security, NOT cross-process parity:** no consumer anywhere recomputes
  this digest independently and compares values, and no 64-hex constant pins
  the engine2d atlas payload. The digest is written into receipts, but the
  checker only validates hex shape and warm==cold within the same receipt.

The one recompute-and-compare in the tree —
`test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:415`,
`native.atlas_payload_sha256 == sha256_u8_hex(evidence_alpha)` — belongs to the
**engine3d** adapter's alpha-channel digest
(`src/lib/gc_async_mut/gpu/engine3d/vulkan_font_adapter.spl:174`), a different
writer over different bytes. **It was deliberately left untouched.** The
engine2d evidence class in that same spec has no `atlas_payload_sha256` field
at all.

## Fix

`_vulkan_font_atlas_payload_digest(pixels, width, height)` in
`backend_vulkan_font.spl`. Still a **real SHA-256** producing the identical
64-char lowercase hex shape, but it is no longer fed 4 MB: every pixel is folded
into a 128-bit four-lane fingerprint (unrolled by 4, no per-element branch),
and SHA-256 is then taken over that fingerprint plus atlas geometry
(`len`, `width`, `height`).

Coverage is unchanged — **all 1024x1024 pixels still contribute**, so any atlas
mutation still moves the token — and the element index is mixed into each lane
so position matters.

Verified sensitivity (interpreted, full 1024x1024 atlas):

| property | result |
|---|---|
| determinism (rebuild identical atlas) | equal |
| single pixel changed | differs |
| two pixels swapped (same multiset) | differs |
| one pixel shifted by 1 index (crosses lane) | differs |
| output shape `.len() == 64` lowercase hex | true |

Rendered output is unaffected by construction: the change touches only the
evidence token. `atlas_payload = _vulkan_font_pixels_to_bytes(batch.atlas_pixels)`
is still built and still uploaded byte-for-byte via `vulkan_sffi_copy_to_buffer`;
no pixel, quad, dispatch or readback path was modified. Diff is +79/-1 in one
file.

## Why not the other options

- **Cache / dirty flag:** already present and already correct. It does not help,
  because the *cold* cost is the problem.
- **Hash only the dirty rect:** would silently stop detecting changes elsewhere
  in the atlas — exactly the "slow guarantee traded for a silent one" failure
  this repo has been fighting.
- **Route to a native SHA-256:** would preserve the digest value exactly and is
  the ideal fix, but **no byte-buffer digest extern is registered for the
  interpreter**. `rt_file_hash_sha256` / `rt_package_sha256` take a *path*;
  `rt_sha256_new/write/finish` exist natively
  (`src/compiler_rust/runtime/src/value/sffi/hash/sha256.rs`) but are AOT-only,
  absent from `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
  Wiring one up spans ~7 Rust-seed files and needs a bootstrap rebuild — a
  separate lane, and against the standing "fix .spl not Rust" rule.
  **Follow-up:** registering `rt_sha256_*` for the interpreter would let this
  site (and `font_registry`, and the engine3d adapter) return to a plain
  full-buffer SHA-256 at native speed.

## Provenance

Measured in the shared working copy at `9dcd16644b8`, **76 commits behind
origin** (`5b4f0b478007975193c863225c387c1ebf4eb61f`). Origin tip does **not
compile** — unrelated `translate_call` trait break, filed at
`doc/08_tracking/bug/mir_to_llvm_translate_call_trait_break_2026-08-04.md` — so
the shared WC is the only testable base. The WC copy of
`backend_vulkan_font.spl` was verified **byte-identical to origin tip** before
editing, so this change applies cleanly to current origin content.

---

# Follow-up (2026-08-04): `rt_sha256_*` registered for the interpreter

- **Status:** DONE. The recorded follow-up above ("registering `rt_sha256_*` for
  the interpreter would let this site, `font_registry`, and the engine3d
  adapter return to a plain full-buffer SHA-256 at native speed") is landed.
- **Changed:** `src/compiler_rust/compiler/src/interpreter_extern/sha256.rs`
  (new) and `interpreter_extern/mod.rs` (five dispatch entries + a guard test).
  **No `.spl` was changed** — see "Recommendation" below for why.

## Why the family was AOT-only — the actual reason

Two independent reasons, only the first of which is a one-line omission:

1. **No `EXTERN_DISPATCH` entry.** `interpreter_extern/mod.rs` registered the
   entire `rt_sha1_*` family (8 entries, `crypto.rs`) and *none* of
   `rt_sha256_*`.
2. **The dynamic fallthrough could never have carried it.** An unregistered
   extern falls through to `dynamic_sffi::try_call_dynamic`, which `dlsym`s the
   symbol out of the runtime library and coerces every argument *and* the
   return value through `i64`. The native signatures cannot survive that:
   `rt_sha256_write(handle: i64, data_ptr: *const u8, data_len: u64)` needs a
   real byte buffer, but an interpreted `[u8]` is a `Vec<Value>`, and
   `rt_sha256_finish(handle) -> RuntimeValue` returns a **packed
   `RuntimeValue`**, not an `i64`. So the fix is not "link harder" — the family
   needs interpreter-native handlers, exactly as `rt_sha1_*` already has.

**Verified by value, not by absence of error.** The "unregistered extern returns
nil silently" trap does not apply here: an interpreted `rt_sha256_*` call did
not silently return nil, it failed hard. Control probe, run against the built
binary with `rt_sha256_finish_bytes` (deliberately left unregistered — see
below), which is the exact pre-change state of the whole family:

```
$ SIMPLE_EXECUTION_MODE=interpret simple run unreg_probe.spl
error: semantic: unknown extern function: rt_sha256_finish_bytes
```

## What is registered

`rt_sha256_new`, `rt_sha256_write`, `rt_sha256_finish`, `rt_sha256_reset`,
`rt_sha256_free` — the five whose observable behaviour is identical in both
lanes, so `.spl` written against them behaves the same interpreted and compiled.

**Deliberately NOT registered:** `rt_sha256_finish_bytes` (the native form packs
32 raw non-UTF-8 bytes into a runtime string; no interpreter `Value` reproduces
that without lossy corruption or a cross-lane type divergence) and any one-shot
`rt_sha256_hex` (no native counterpart, so a `.spl` caller would run
interpreted and fail to link AOT).

Byte extraction is **strict** — a non-byte array element is a hard error, never
a dropped element. `crypto.rs::rt_sha1_write` `filter_map`s non-`Int` elements
away, which silently hashes a *shorter* buffer when handed a real `[u8]` (whose
elements are `Value::UInt { width: 8 }`, not `Value::Int`). That latent SHA-1
defect is noted here but not changed in this lane.

## KAT verification

Expected values transcribed from the **published standard** — RFC 6234 §8.5
(TEST1 / TEST2_1, which reproduce FIPS 180-4 Appendix B.1/B.2 verbatim) and the
NIST CAVP short-message vector `Len = 0` — **not** derived from this
implementation.

Run through the real interpreter (`SIMPLE_EXECUTION_MODE=interpret`, the
release-built seed, calling the externs directly):

| input | digest | verdict |
|---|---|---|
| `""` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | PASS |
| `"abc"` | `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` | PASS |
| `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"` | `248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1` | PASS |
| negative control (`"abc"` vs all-zero hex) | — | FAIL, as required |

The negative control is there because a probe that only ever prints PASS proves
nothing; it fails, so the comparison is live.

Nine Rust unit tests cover the same vectors plus multi-chunk streaming, `[u8]`
arrays of `UInt{width:8}`, handle independence, reset, free, unknown-handle
errors, and overlong-`len` errors. **Sabotage check:** flipping one hex digit of
the `"abc"` constant made `streaming_matches_published_vectors` FAIL with
`left: "ba7816bf…"` (the true published value) — so the assertion is live and
the implementation independently produces the standard's answer. Reverted.

The strongest correctness evidence is cross-implementation: on a real 4 MB
`[u8]`, the extern and the pure-Simple `sha256_u8_hex` produce **the same
digest** (`e6d6899207ceb4cabe72b20d4704be0ec2764663f1fdc61c9e87cf94f81bc11e`,
`AGREE=yes`). Two independent implementations agreeing on 4,194,304 bytes.

## Measurements (external `/usr/bin/time`, never in-language)

`SIMPLE_EXECUTION_MODE=interpret`, release seed. `build` allocates the `[u8]`
and does nothing else; the digest step is the difference.

| buffer | build only | + pure-Simple `sha256_u8_hex` | + native extern |
|---|---|---|---|
| 64 KB | 0.21 s | 9.14 s | 0.19 s |
| 128 KB | — | 18.91 s | — |
| 4 MB (4,194,304 B) | 7.68 s | 754.09 s (`both` run) | 8.21 s |

Digest step alone:

| buffer | before | after | ratio |
|---|---|---|---|
| 64 KB | 8.93 s (**7.34 KB/s**) | below build-run noise (< 0.05 s) | > 180x |
| 128 KB | 18.70 s (**7.01 KB/s**) | — | — |
| 4 MB | 745.9 s (**5.6 KB/s**, box under heavy parallel load) | **0.53 s (7.9 MB/s)** | **~1,400x** |

The 7.34 / 7.01 KB/s pair reproduces the originally filed ~7.2 KB/s and confirms
linearity. The residual 0.53 s at 4 MB is the interpreter walking 4,194,304
`Value`s across the extern boundary, not SHA-256 itself.

## Recommendation on the fingerprint workaround — RECOMMEND, do not revert yet

The `_vulkan_font_atlas_payload_digest` fingerprint in
`backend_vulkan_font.spl` is **left in place**. It can now be reverted to a
plain full-buffer SHA-256 that is fast enough (0.53 s for the whole atlas, and
the digest is byte-identical to `sha256_u8_hex`, so the 64-char lowercase hex
shape that `vulkan_font_stage_evidence_ready` and
`check-macos-gpu-2d-live-evidence.shs` gate on is preserved by construction).
But there is one unresolved cross-lane hazard that must be settled first, and it
is not verifiable from this lane:

**`std.infra.hash.Sha256Hasher` cannot be the vehicle.** Its `write` is
`rt_sha256_write(self._handle, data as i64, len(data))` — the AOT `(ptr, len)`
ABI. Interpreted, that is a hard semantic error, measured:

```
error: semantic: type mismatch: cannot cast array to i64
```

So an interpreted caller must pass the array itself, while the compiled lane
wants the pointer cast. Any `.spl` helper shared by both lanes needs that split
resolved (or the extern declaration typed `[u8]` and the AOT lowering verified
to still produce a valid buffer). Reverting the fingerprint without settling
this risks trading a slow-but-correct token for one that works interpreted and
breaks compiled — and the vulkan font lane cannot be run to completion here to
prove otherwise. Recommended sequencing:

1. Add a `.spl` digest helper whose argument passing is verified in **both**
   lanes (interpreted probe + an AOT `native-build` probe), by value.
2. Then revert `_vulkan_font_atlas_payload_digest` to
   `sha256_u8_hex`-equivalent full-buffer SHA-256 through that helper, and
   re-measure the atlas upload end to end.
3. `font_registry.spl`'s `digest_route_interp` fallback
   (`bytes_to_hex(sha256_bytes(_u8_blob_to_i64_array(blob)))`) and the engine3d
   `vulkan_font_adapter.spl` alpha digest are the other two beneficiaries and
   should ride the same helper.

## Provenance

Measured in a pristine detached worktree at origin tip
`adefa51eda93938ebc753733d40a633411e638f9`, zero uncommitted `src/` before the
change. Seed built from that worktree (`cargo build --release -p simple-driver
--bin simple`); every `.spl` number is `/usr/bin/time` around a whole process.
The box was running several other agent sessions during the 4 MB `both` run,
which inflates its absolute wall time — the 64 KB / 128 KB pair is the clean
rate measurement.

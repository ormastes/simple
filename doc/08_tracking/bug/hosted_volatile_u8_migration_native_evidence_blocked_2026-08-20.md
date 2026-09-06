# Hosted volatile-u8 migration native evidence blocked — 2026-08-20

## Status

HOLD. Production-path correctness is implemented in isolated base
`b7ab12511c4b58d070ea7f40c9aa741d9995cc1c`, but current-source native,
coverage, mutation, and performance acceptance requires an admitted Stage 4
compiler/runtime. The authoritative worktree remains untouched. This candidate
must not be integrated from diagnostic evidence alone.

## Corrected production boundary

- `volatile_ops` no longer calls the undeployed `rt_is_interpreter_runtime`.
- A caller must first call `hosted_volatile_u8_admit`; only the admitted
  creator thread makes `hosted_volatile_u8_current_owner_admitted()` true and
  selects the bounded u8 fallback. A non-admitted native caller keeps the
  unchanged `rt_volatile_read_u8` / `rt_volatile_write_u8` ABI.
- The public `HOSTED_INTERPRETER_DOMAIN` scalar and every caller-supplied
  domain argument were deleted. The private canonical owner stores its
  capability in the existing `rt_thread_local_*` owner. Each operation checks
  the current TLS slot; callers cannot forge ownership by copying a public
  integer.
- The Rust tree-walk u8 read/write providers and dispatch registrations remain
  removed. Source guard counts are both zero.

## Evidence obtained

- Real interpreted production call chain:
  `admit -> register -> volatile_read_u8/volatile_write_u8 -> hosted fallback`.
- Frozen C/Simple output parity: PASS, 31/31 rows, identical SHA-256
  `6fb7bcb6f2d93e214c651372b8696023de8d257ebda26b61dc8d356c07254b6c`.
- The vectors cover admission/duplicate admission, creator ownership,
  zero/duplicate/capacity registration, unknown read/write/unregister,
  u8 normalization, mutation, middle-entry unregister with both retained
  sides, reset, and generation transitions `0 -> 1 -> 4 -> 5 -> 6 -> 7 -> 71`.
- The standalone integration probe exits 0 and reports the exact generation
  sequence above. `git diff --check` is clean.
- Source guards: Rust u8 provider definitions `0`; Rust u8 dispatch entries
  `0`; `rt_is_interpreter_runtime` references in the facade `0`.

These are diagnostic/interpreter rows, not native acceptance evidence.

## Three-cycle stop record

1. The focused unit ran and exposed a test-shape error: `thread_spawn` requires
   a closure rather than a bare function reference.
2. With the closure fixed, all earlier assertions passed but the final
   generation assertion reported `73` rather than `71` when the cross-thread
   rejection probe was present. The standalone production probe reports `71`.
3. Making every capacity-loop mutation explicitly single-evaluation produced
   the same unit-only `73` result. Per the mandatory three-cycle cap, no fourth
   fix/retry was attempted.

The current-source Cargo test is also unavailable in this sparse checkout: the
runtime build closure lacks the C archive inputs and fails while creating
`libruntime_sffi_c.a`. The failed build was terminated; it is not a source
verdict.

## Frozen candidate hashes

- owner: `68158f39b377c8cdd9f8324a433bf27fda9aa55f5fad4dafbc783b830970e86e`
- facade: `99a922116f50618295751990d9fd25f7816c48d5268640217a6530880619b636`
- focused unit: `8536ed10573261bedc3afdc8830e8c3443d0375553c037dc82e320fd4c8f5cd4`
- Simple parity probe: `47953850ea2829575a8ec3a0ab1f3607436cdd98f295d9481f194803f9cce0d8`
- C parity oracle: `7b2aaab2ef4c0bf451b11cf565b0ecb4bb4052dbca22edc62e827dd036f2cf1a`
- Simple perf probe: `f1d2ad50dab2bcf4633d59c6e455a011478992eb1a54fa410712c3ed6ca18c50`
- C perf oracle: `939fa49002ecfd8dd85743e73b9f33f7972bcf6e3a8cc345418a6a5930108d54`

## Required Stage 4 continuation

From these exact hashes, use an admitted current-source pure-Simple Stage 4
compiler/runtime and run each acceptance check once:

1. focused unit plus compiler-produced decision/branch coverage; require 100%;
2. compiled real-facade parity against the frozen C oracle;
3. bounded mutation-kill cases for ownership, normalization, retained
   compaction, generation, duplicate, capacity, and unknown-address decisions;
4. warm comparable native C/Simple I/O medians using the frozen perf probes;
   require identical checksum and Simple/C `<=3.0x`;
5. exact authoritative preimage/hunk recheck and independent xhigh review.

Only an envelope containing all five green rows may say GO. Until then the
verdict is HOLD.

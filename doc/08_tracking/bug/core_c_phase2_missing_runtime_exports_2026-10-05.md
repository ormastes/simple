# Phase 2 runtime exports and NUL-preserving process capture

Status: native provider regressions and Phase 2 relink pass; Hello blocked.

The immutable Linux CI seed from source `817fef0`, SHA256
`e5d49e42816843002f11a6fbd5f619168063253c9b2d8a91a4ae2f38111d380d`, compiled
all 1198 source objects for release `17cdbe022a6`, then failed to link the
core-C bootstrap runtime. Missing symbols were `rt_any_to_int`,
`rt_shared_parse_cell_read_v1`, and `rt_value_truthy`. The retained output is
`build/review/item5-linux-phase2-composition-continuation-3.log` in the host
checkout; its RSS receipt records normal completion, exit 1, and peak
1250728 KiB. This is an ABI/provider failure, not memory exhaustion.

## Repairs

- Backport the existing C and Rust `rt_any_to_int` providers and declaration from
  main commit `1bc4bd4702b7122d2bcce60af26640e5b535fe6f`. This decodes tagged
  erased receivers. Aliasing `rt_to_int_dynamic` would return tagged integer
  bits unchanged and is incorrect.
- Export the existing core-C truthiness implementation through the compiler's
  `int8_t rt_value_truthy(int64_t)` ABI. Match Rust's heap-u64 zero handling
  before the generic heap-pointer branch; retain float, integer, special,
  and ordinary heap truthiness semantics.
- Share the existing bounded no-follow parser-cell read through
  `runtime_shared_parse_cell_private.h`. Both mutually exclusive core-C and
  narrow Rust runtime owners include this exact implementation. Adding all of
  `runtime_secure_staging.c` to the core-C archive would duplicate existing
  ABI, directory, file, and staging exports.
- Preserve POSIX stdout/stderr byte lengths from fork capture through runtime
  string construction, including incomplete-capture and timeout markers. The
  prior `strlen` conversion discarded the first NUL and all subsequent bytes.
  Keep the existing head/tail output bounds and strict workaround Git parser.

The extracted reader body is byte-identical. Its two private path helpers,
including Windows extended-length path handling, move with it. Header
freshness is bound by the Rust native runtime input inventory, canonical
core-C capsule header list, and Cargo runtime build rerun declaration.
The immutable seed continues compiling `runtime_native.c` from the checkout,
so this repair is available without substituting Rust runtime archives or
changing the producer binary.

## Executed evidence

Clang 23.1.1 under WSL compiled the actual `runtime_native.c` with
`-std=gnu11 -O1 -ffunction-sections -fdata-sections
-DSIMPLE_CORE_C_STANDALONE=1`. Focused executables link that object with
`-Wl,--gc-sections -lpthread -ldl -lm`, without duplicate-symbol suppression.

- `rt_value_truthy_selfcheck.c`: 17 cases pass, including nil/booleans,
  positive and negative integers, signed float zero, nonzero float/NaN,
  heap-u64 zero/nonzero/high bit, wide integer, text, and tagged null heap.
- `rt_any_to_int_selfcheck.c`: 15 tagged conversions, an actual array slot,
  and distinction from raw dynamic integer identity pass.
- Existing `rt_shared_parse_cell_read_v1_selfcheck.c` passes against the
  narrow owner; its `SIMPLE_TEST_CORE_RUNTIME` mode also passes against the
  real core-C text ABI. Both exercise bounded file content, oversize refusal,
  symlink refusal, and missing-file behavior.
- `llvm-nm --defined-only` finds all three exports in the compiled native
  object. Extraction comparison and scoped whitespace validation pass.
- Rust `test_any_to_int_decodes_tagged_values`: one actual native test passes,
  zero failures, 1336 filtered, using an isolated Cargo cache and the
  coordinated working source at release `d5df0cb6` (5m09s compilation).
- `runtime_process_nul_capture_selfcheck.c`: actual native executable passes
  embedded/trailing NULs on both streams, exit 23, exact two-byte head/tail
  retention plus omission markers, timeout with exit -1 and child reaping,
  and empty-capture length reset. It links the real process, fork, memtrack,
  and core-C providers. Windows capture was not changed or validated here.

These are native Linux provider tests, not a Phase 2 compiler admission,
Windows execution proof, full bootstrap, or DB/web AVX512 result.

## Repaired producer outcome

The frozen ten-file runtime patch SHA256
`63185d0b6360e74a8c051cd7c1200b396e58a10246fdb613604ef9b2b57d7968`
was applied to release `d5df0cb60b91fa0e799ba3ca46c8d3d0bde54ef3` for the
cache-preserving producer run. It linked successfully: two objects compiled,
1196 reused, zero failed, 135.1 seconds total, peak RSS 1222736 KiB with
enforcement enabled. The resulting Phase 2 SHA256 is
`51b7c4acc51e04920c975405122674d57d4931911469bf68ca7b5766ec5b5bb1`.

The canonical Hello gate then failed source inventory admission because its
legacy fixture lives under `scripts/`, outside the admitted `src`/`test`
families. The coordinator also reported truncated Git status output; the
POSIX process result path uses `strlen` on NUL-delimited output. Those are
separate admission/capture bugs; successful linking is not compiler admission.

The exact Git invocation in that source checkout returned exit 0, 468 bytes,
10 NUL-delimited records, and a final NUL. The first NUL was at byte 59;
the former process result conversion therefore returned only that first
record without its delimiter. The new private C length bridge carries the
captured byte count, as exercised by the native binary-capture regression;
the produced compiler has not yet qualified Hello with this repair.

The C/Rust ABI pair satisfies the runtime single-lane gate's pairing model.
A pure-Simple twin for erased integer conversion remains architectural debt;
this backport does not claim dual-run Simple coverage or full bootstrap admission.

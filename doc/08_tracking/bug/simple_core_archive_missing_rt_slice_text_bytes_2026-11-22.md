# simple-core archive lacks rt_slice_text_bytes, so the seed rejects it for every app (2026-11-22)

Status: FIXED in source (this change).

## Symptom

New Phase 1 seed (release `6816f70c47e`). `check-simple-core-runtime-smoke.shs` produced
`build/essential-apps/simple-core/libsimple_runtime.a`, sha256
`b27d686fa9e38de4515c9af91299525c0067d38f875429080d10c7f8b2771d91`. Every essential app was then
built with `--runtime-bundle simple-core` and `SIMPLE_SIMPLE_CORE_PATH=<that archive>`, with no
`--runtime-path`. Each one failed after its full compile (about 20 min for `cs`):

```
Build failed: native-build requested `simple-core` for `.../src/app/llm_caret/cs_main.spl` but no
simple-core runtime archive was found. Provide SIMPLE_SIMPLE_CORE_PATH/SIMPLE_CORE_RUNTIME_PATH ...
```

## Root cause

The seed finds the archive (`find_simple_core_runtime_library`, which reads
`SIMPLE_SIMPLE_CORE_PATH`). It then discards it in `find_abi_complete_simple_core_runtime_library`
(`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:1538`), unless the archive
defines every `CORE_REQUIRED_RUNTIME_SYMBOLS` entry
(`src/compiler_rust/common/src/runtime_symbols.rs:118`).

`llvm-nm -g --defined-only` against the list found one of 86 missing: `rt_slice_text_bytes`.
`cd571d8df1a` added it to the required list (byte-offset `.slice(a, b)`/`.substring(a, b)` method
entry). Twins exist in `src/runtime/runtime_native.c:6298` and the Rust runtime. No twin was
added to the pure-Simple `src/runtime/simple_core/core_string.spl`. The archive script's own
required list is shorter and hard-coded, so it did not catch the gap. The seed's message names
the archive as missing rather than incomplete, which hides the cause.

## Fix

- `src/runtime/simple_core/core_string.spl`: add `pub fn rt_slice_text_bytes`, mirroring the C
  twin. Text receivers are cut at byte offsets clamped to `0..=byte_len()` and copied raw. Any
  other receiver, and a step below 1, goes to `rt_slice`.
- `scripts/check/check-simple-core-runtime-smoke.shs`: after building the archive, check every
  `CORE_REQUIRED_RUNTIME_SYMBOLS` entry, parsed from `runtime_symbols.rs`. It fails with
  `error=missing_core_required_symbol:<name>`. An unreadable list is ERROR, exit 2.

## Specs

- Reproducing: the new archive-time gate. Run over the pre-fix archive (sha256 above), the same
  list diff reports `missing=1 rt_slice_text_bytes`.
- Generalization: the gate covers all 86 required symbols, so any future required symbol without
  a simple-core twin fails at archive time.
- Open follow-up for the seed owner: the "no simple-core runtime archive was found" message should
  name the missing required symbols when an archive was found but rejected.

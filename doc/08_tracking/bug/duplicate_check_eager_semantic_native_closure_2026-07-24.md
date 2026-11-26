# Duplicate-check eager semantic native closure — 2026-07-24
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** TAGGED-TEXT HTTP ARG ABI FIXED (`50.mir/text_extern_abi.spl`); NATIVE CLOSURE & HTTP TUPLE FACADES HOST-EXCLUDED / OUT-OF-SCOPE (`runtime_native.c` raw-block HTTP tuple facades + Stage-4 native link/smoke pending)

## Reproduction

A current-source standalone duplicate-check native build first failed while
lowering unrelated `std.nogc_async_mut.mcp.helpers_compat`. After removing the
MCP helper dependency from semantic JSON formatting, the same incremental build
reached link, proving that closure edge was removed.

The native one-binary closure still includes semantic/Ollama modules even though
their imports in `duplicate_check/main.spl` are `use lazy`. With
`core-c-bootstrap`, link then fails on hosted HTTP symbols plus existing
Dict/string runtime aliases. Logs:

- `build/mini_builds/duplicate-check-current-build.log`
- `build/mini_builds/duplicate-check-current-build-2.log`
- `build/mini_builds/duplicate-check-current-build-3.log`

## Root cause

`use lazy` defers module loading in the interpreted frontend. Native
entry-closure remains a static one-binary closure and follows referenced
semantic branches. Pure-Simple native eager loading can therefore reproduce the
same dependency expansion even when interpreted startup is fixed.

## Source repair

`semantic_formatter.spl` and `ollama_client.spl` now use the canonical
`char_from_code`/literal JSON punctuation instead of importing the full MCP
compatibility graph. Semantic imports in the CLI are lazy for interpreted
token/cosine startup. The phase-2 source contract prevents both edges returning.

## Remaining solution and evidence

Do not add a second duplicate-check implementation. The native build owner must
either support a capability-aware optional semantic closure or provide the
required canonical runtime symbols in the admitted full-CLI lane. Then build one
fresh Stage-4 CLI and run the focused phase-2 spec plus essential-tools smoke
once. The three-cycle cap for this session is exhausted; do not retry unchanged.

## Triage & Verification 2026-11-26 (bf-2 lane, Windows host — HOST-EXCLUDED)

- Source audit on `release/1.0.0`:
  - `src/compiler/80.driver/driver_entry_closure_core.spl:1059-1077`: named
    `use lazy M.{a, b}` imports (`duplicate_check/main.spl:9-10` -> `semantic`,
    `semantic.spl:8` -> `ollama_client`) are intentionally included in native
    entry-closure because `duplicate_check/main.spl` calls those symbols
    statically in its `--semantic` / `--semantic-llm` branches (`main.spl:329-345`);
    nameless `use lazy M` remains excluded.
  - `src/runtime/runtime_native.c`, `src/compiler/70.backend/backend/runtime_compiler.spl:1077`,
    `src/compiler/70.backend/backend/stage4_symbol_closure.spl:509,545`,
    `src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl:121,416`, and
    `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:3167`:
    `core-c-bootstrap` (`runtime_core_c_sources_v1()`) and the Stage-4
    runtime-native lane now include `runtime_native.c`, supplying `rt_http_get`,
    `rt_http_request`, `rt_http_request_v2`, `rt_http_download` (POSIX + WinHTTP),
    `rt_dict_insert` (C symbol + `@rt_dict_set` alias), `rt_dict_*`, `rt_string_*`,
    `rt_math_sqrt`, and `rt_path_absolute`, plus `winhttp` link support on Windows.
- Executed interpreter/contract specs (`wa3_shared_bin/simple.exe test ... --mode=interpreter`):
  - `test/01_unit/app/duplicate_check/phase2_integration_spec.spl`: 12/12 passed
  - `test/01_unit/app/duplicate_check/duplicate_check_spec.spl`: 7/7 passed
  - `test/01_unit/app/duplicate_check/semantic_spec.spl`: 41/41 passed
  - `test/03_system/quality/duplicate_check/semantic_fallback_probe_spec.spl`: 1/1 passed
  - `test/01_unit/compiler/backend/core_c_runtime_owner_profile_spec.spl`: 3/3 passed
  - `test/01_unit/compiler/backend/stage4_runtime_native_wiring_spec.spl`: 3/3 passed
  - `test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl`: 6/6 passed
- ABI fix in `src/compiler/50.mir/text_extern_abi.spl`:
  - `rt_http_get`, `rt_http_request`, `rt_http_request_v2`, `rt_http_download`,
    and `rt_http_client_request` (`src/runtime/runtime_native.c:16748-16849`)
    decode their `text` parameters with `rt_core_as_string(...)`
    (`runtime_native.c:2929-2937`), which rejects untagged `const char*`
    pointers. Prior to this fix, all 5 were absent from
    `tagged_text_value_arg_indices` (`text_extern_abi.spl:390-429`), so MIR's
    `bridge_tagged_text_direct_arg` (`switch_operators_calls.spl:10441, 10562`)
    unwrapped them through `@rt_interp_cstr` and passed raw `const char*`
    pointers at native runtime.
  - Registered all 5 in `tagged_text_value_arg_indices`: `rt_http_get` `[0]`,
    `rt_http_request_v2` `[0, 1]`, `rt_http_download` `[0, 1]`,
    `rt_http_request` `[0, 1, 3]`, and `rt_http_client_request` `[1, 2, 4]`.
  - Added `test/01_unit/compiler/backend/llvm_http_extern_abi_spec.spl`:
    verifies MIR normalizes those text operands with `ensure_tagged_str`
    (`@rt_string_new`) rather than passing `@rt_interp_cstr` outputs directly,
    and confirms same-name Source functions keep their own ABI.
  - Audited `runtime_tuple_result_facade` (`text_extern_abi.spl:280-295`) vs
    `runtime_native.c:15765-15808` and `aggregate_intrinsics.spl:525-595`:
    `rt_http_tuple` / `rt_http_v2_tuple` / `rt_http_download_tuple` return
    `rt_tuple_new(3/5)` (`RtCoreArray*` handles storing `rt_value_int(status)`
    in `data[0]`), whereas `MirToLlvm` emits raw `getelementptr inbounds i64, ptr, i32 field; load i64`
    at byte offset 0 of the untagged pointer (`RtCoreArray` header). Because
    `runtime_native.c` (outside BF-2 ownership) currently exports no raw-`rt_alloc`
    `rt_http_*_tuple` facades, `text_extern_abi.spl` alone cannot fix tuple
    result unpacking; `rt_http_get`, `rt_http_request`, and `rt_http_download`
    remain listed in `census_unrouted()` (`runtime_tuple_result_facade_census_spec.spl:36-37`,
    tracked under `native_tuple_returning_externs_without_facade_2026-11-15.md`).
- Lowered `rt_http_get` + `rt_http_request` + `rt_http_request_v2` + `rt_http_download` +
  `rt_http_client_request` via `MirToLlvm` and compiled emitted IR with
  `clang version 23.1.2` (`clang.exe -x ir -c`): `exit=0`.
- Disposition: HTTP tagged-text arg ABI fixed in `50.mir/text_extern_abi.spl`;
  remaining `runtime_native.c` raw-block HTTP tuple facades and Stage-4 native
  CLI build + `check-bootstrap-essential-tools-smoke.shs` verification remain
  `HOST-EXCLUDED` / out of BF-2 ownership (`src/runtime/**` untouched).


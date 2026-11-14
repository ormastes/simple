# Hosted text-to-bytes provider ABI mismatch

Status: fix implemented; focused Linux provider regression passed; review/landing pending.

The ordinary hosted bundle links `runtime.c` before `runtime_native.c` with duplicate definitions permitted. The former accepted a C string and returned a private buffer pointer, while the Simple extern and native twin require tagged text and a canonical packed-byte array. Therefore `text_to_bytes("pkg")` yielded an invalid array handle. This is a provider ABI defect, not a TLDR codec defect.

The hosted twin now accepts the canonical `int64_t` text value and delegates to native string data/length and `rt_bytes_from_raw`. Its header records the same ABI. Existing platform guards and weak-symbol policy remain intact; no global linker ordering or unrelated symbol policy changes.

## Focused evidence

On Linux AArch64, actual current-release runtime objects reproduce failure code 11 with the original hosted provider first. The patched real providers pass ASCII, embedded NUL, UTF-8, empty-array and roundtrip assertions in both duplicate-symbol orders. Run `sh scripts/check/check-hosted-text-bytes-abi.shs`; unsupported hosts return 77. The script uses real runtime objects, not mock arrays or strings.

Retained local evidence: `/tmp/hosted-text-bytes-pair-20261114`, including `run-baseline2.log` (exit11), `check-script.log` (both orders PASS), source objects and link logs. A pinned admitted pure-Simple P2 compiler SHA256 `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42` separately reproduced the default-bundle failure with indexed-byte assertions. Its core-c composition passes. Initial current-source override attempts failed because the sparse checkout omitted backend-plugin and counterpart SDK headers. After materializing those exact tracked dependencies, the final default-bundle compile and native indexed-byte test both returned zero (`compile-default-green-complete.log`, `run-default-green-complete.log` in `/tmp/trace-text-provider-newp2-20261114`). Six bounded producer attempts total; no further retries. The pinned compiler/current runtime integration is scoped evidence, not whole-runtime or Phase 3 qualification.

The SFFI pointer/host audits against the sparse candidate report incomplete inventory/baseline findings. The on-demand C-contract audit is UNTESTED because unrelated `rt_stderr_write` declarations conflict; it is not counted as PASS. Astra's source-only backlog audit against full checkout `671d5545201` reported existing inventory drift (400/399 variants, 3762/3546 migrations). None substitutes for native provider execution.

Windows and macOS source guards are preserved; native qualification on those platforms is not claimed. Phase 3/full CLI, broad compiler/library and MCP tests are not implied by this scoped C runtime regression.

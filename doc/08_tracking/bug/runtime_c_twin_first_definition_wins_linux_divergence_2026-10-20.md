# runtime.c twins: Linux first-definition-wins diverges from Darwin weak-twin resolution

- **Date:** 2026-10-20
- **Status:** open
- **Found by:** macOS host-gpu tool link work on `release_phase3` (weak-twin fix `SPL_RUNTIME_NATIVE_TWIN`)

## Problem
37 `rt_*` functions are defined both in `src/runtime/runtime.c` (24) / `src/runtime/platform/unix_common.h` (13, included only by `runtime.c`) and in `src/runtime/runtime_native.c` (`rt_process_wait`: `runtime_process.c:3322`).

- **Darwin** (after the weak-twin fix): the `runtime.c` copies are weak, so the `runtime_native.c` / `runtime_process.c` bodies win.
- **Linux / FreeBSD**: links pass `--allow-multiple-definition` (`native_linking.spl:144-147`), so the FIRST definition on the link line wins — `runtime.c` comes first, so the `runtime.c` bodies are used.

Same source, different runtime behavior per platform. Concrete hazard: `runtime.c:4182 rt_text_to_bytes(const char*)` vs `runtime_native.c:8687 rt_text_to_bytes(int64_t text_value)`; stdlib externs (`tls/handshake.spl:24`, `hkdf.spl:22`) pass tagged text, which matches only the `runtime_native.c` body. The five `rt_bdd_*` in `runtime.c` are no-op stubs, while `runtime_native.c` has the real implementations.

Also: `llvm_hosted_allow_duplicate_definitions` (`llvm_native_link_orchestrator.spl:57-61`) claims Darwin allows duplicates, but `unresolved_symbol_flags_for_cc("Darwin") == []`.

## Fix direction (owner decision)
Make `runtime_native.c` the single owner on every platform: apply `SPL_RUNTIME_NATIVE_TWIN` as weak on ELF as well (GNU/LLD honor weak vs strong regardless of order), or delete the `runtime.c` copies once every bundle that compiles `runtime.c` also links `runtime_native.c`. Then correct `llvm_hosted_allow_duplicate_definitions` for Darwin.

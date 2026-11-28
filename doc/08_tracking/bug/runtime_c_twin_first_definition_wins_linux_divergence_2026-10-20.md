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

## Casualty 2026-11-28: `rt_bytes_to_text` (sha256_text nil in Stage 2 native binaries)
`runtime.c:3938 rt_bytes_to_text` copied `rt_array_data_ptr` bytes verbatim; `runtime_native.c` narrows a tagged-slot `[u8]` per element. With `runtime.o` first on the link line the `runtime.c` body ran, so a slot-layout `[u8]` (`[0u8; 64]`, a literal, `push`) became the low bytes of `value << 3` (`[97u8, 98u8, 99u8]` -> `08 03 00`), and any such byte >= 0x80 made strict UTF-8 return NIL. `_sha256_digest_hex` builds its 64 hex bytes that way, so `sha256_text` returned nil for every input: `group_process_child_argv_digest_v2` was empty and the launch-template generator printed `TEMPLATE ERROR: invalid stream digest`. The seed-built compiler was unaffected (its core-C runtime does not compile `runtime.c`).

Fixed in the twin only (the single-owner decision above is still open): it now goes through `rt_array_bytes_validate` / `rt_array_bytes_copy_checked`. `test/rt_bytes_to_text_layouts_selfcheck.c` had only ever linked `runtime_native.o`; it now runs with `runtime.o` first and last (see the audit below).

## Audit 2026-11-28: all twins

The "37" above came from reading source. Measured with `nm` on the objects of the ordinary bundle (`sources` in `runtime_compiler.spl`, clang, both define sets), **95** global symbols are defined by two objects. Winners were read from `-Map` output of `ld.lld` and `mold` (identical): a strong definition beats a weak one, otherwise the first object wins.

| definers | binding | ELF winner | count |
|---|---|---|---|
| `runtime.c`, `runtime_native.c` | strong / strong | `runtime.c` | 46 |
| `runtime.c`, `runtime_native.c` | strong / weak | `runtime.c` | 28 |
| `runtime.c`, `runtime_native.c` | weak / strong | `runtime_native.c` | 7 (`rt_enum_*`) |
| `runtime.c`, `runtime_process.c` | strong / strong | `runtime.c` | 4 |
| `runtime.c`, `runtime_memory.c` | strong / strong | `runtime.c` | 1 |
| `runtime_native.c`, `runtime_timestamp.c` / `runtime_sdl2.c` | weak / strong | the strong owner | 9 |

Other lanes, by reading the source and the driver, not by linking there:

- The core-C bundle (seed-built compilers, Stage 4, a plain Windows link) does not compile `runtime.c`; built here it has no strong/strong pair.
- Mach-O: only the copies marked `SPL_RUNTIME_NATIVE_TWIN` are weak, and for those the other definer runs. Unmarked strong `runtime.c` copies (`rt_open_fd`, `rt_close_fd`, `rt_secure_temp_dir`, the three `rt_process_*`, `spl_f64_to_bits`, ...) and all 28 strong-vs-weak pairs resolve to `runtime.c` there as on ELF, where the platform `#if`s define both at all.
- COFF: a Windows link with native-all keeps the ordinary bundle, so `runtime.c` is compiled there under a strict (no duplicate) link. `runtime.c` then takes `platform_win.h` instead of `unix_common.h`; which twins survive `_WIN32` was not measured.

Bodies were compared as normalized source (the `#if` branch the preprocessor selected) and, for every strong/strong pair with data-dependent behaviour, by calling both bodies in one process on the same inputs (the `runtime.o` copies renamed with `llvm-objcopy --redefine-syms`).

State after this change (95 total):

| result | count |
|---|---|
| identical bodies | 15 |
| benign difference (same answers on POSIX; Windows branches, helper factoring, hardening of invalid input) | 32 |
| weak fallback by design (strong owner wins in any order) | 44 |
| observable difference left open | 4 |

Nine pairs were divergent before it and were fixed in the winning body; they now sit in the rows above.

Fixed (winner was wrong or narrower than its twin; `src/runtime/test/rt_twin_winner_selfcheck.c` failed 10 checks before, passes with `runtime.o` first and last):

- `rt_process_wait`: the `runtime.c` copy reaped with `waitpid` and never recorded the child's rusage, so `rt_process_last_child_peak_rss_kib` stayed empty in ELF hosted binaries. The copy is now weak on ELF too (`SPL_RUNTIME_OWNER_TWIN`); `runtime_process.c` wins.
- `rt_fd_write`: a zero-length write returned -1 and a short write was not continued.
- `rt_dir_create_cpath` (recursive): an existing regular file counted as success; `/` failed.
- `rt_file_lock`: the descriptor was inherited by spawned children (no `O_CLOEXEC`); `EINTR` aborted the wait.
- `rt_file_unlock`: returned true for a descriptor that is not open.
- `rt_open_fd`, `rt_file_read_text_at`, `rt_remove`, `spl_str_ptr`: the `runtime.c` copies read their `text` argument only as a `char*`; the twins also take the tagged value. Latent, not live: none is in `tagged_text_value_arg_indices` (`50.mir/text_extern_abi.spl`), so the compiler passes the `char*` bridge today. They now accept both.

Left open (rows of class `design` in the allowlist):

- **`rt_process_kill`** — three bodies, three contracts. `runtime.c` (ELF winner): SIGTERM, 100 ms, SIGKILL, reap; false for a missing pid. `runtime_process.c` (core-C lane): SIGTERM only, no reap, true for a missing pid, so a child that ignores SIGTERM stays alive. Rust seed: SIGKILL and reap, spawned children only. The ELF winner is the stricter one; which contract `runtime_process.c` should have is an owner decision.
- `rt_file_read_text_at`, `rt_open_fd`: for a `char*` no runtime string owns, `runtime.c` reads it and the `runtime_native.c` decoder rejects it (`rt_file_read_text_at`) or copies it by length.
- `rt_secure_temp_dir`: different random-suffix length in the directory name; same mode and rejections.

Gate: `scripts/check/check-runtime-c-twin-bodies.shs` (wired in `code-idiom-gates.yml`, the step that ran the check it replaces; `--selftest`, 12 fixtures). It compiles the bundle, takes duplicates and winners from `nm`, and fails on any pair whose bodies differ without a row in `scripts/check/runtime_c_twin_allowlist.txt`. A row carries a hash of the winner and both bodies, so an edit to either body or a link-order change fails until the pair is reviewed again. It replaces `check-rt-bytes-to-text-twin-link-order.shs`.

Still open:

- The single-owner decision above. Only `rt_process_wait` was made weak on ELF; the other 78 `runtime.c` winners still depend on link order.
- `scripts/check/check-runtime-bundle-duplicate-symbols.shs` no longer works: it greps `var sources = [`, the declaration is now `var sources: [text] = [`, so it scans 5 files instead of 37, reports every baseline row stale and exits 1. It is unwired (`guard_wiring_optout.txt`). The new gate covers its job; it and `runtime_bundle_duplicate_symbols_baseline.txt` were not removed here because `test/01_unit/compiler/backend/runtime_dynload_owner_source_spec.spl` reads the baseline and three other guard baselines name the script.
- The gate compiles for the host. The duplicate set on Mach-O was derived from the `SPL_RUNTIME_NATIVE_TWIN` markers, not from a Darwin link.

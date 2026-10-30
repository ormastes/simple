# Windows Stage 2 sanity: SCV prime skipped after a compiler change; unhinted link flavor is MSVC

Status: OPEN. Found 2026-10-25 on DESKTOP-5A4V03J (MinGW clang default lane,
`--backend=cranelift`). Related:
[windows_gnu_stage2_qualification_cli_timeout_and_empty_module_cc_2026-10-25.md](windows_gnu_stage2_qualification_cli_timeout_and_empty_module_cc_2026-10-25.md).

## 1. Sanity `p2_add` times out because the SCV prime is skipped

Bootstrap attempt 10 (same tree as attempt 9 plus three MIR-lowering fixes)
rejected its Stage 2 candidate: `frontend smoke exited 124`, probe
`p2_add-build`, `timeout_seconds=180`, `scv_prime_raw_status=not-run`.
Attempt 9 passed the same probe because it ran `scv_prime` first. That run
cold-initialises the compile-event journal. Attempt 10 found attempt 9's
journal and skipped the prime, so `p2_add` paid the first-build cost for the
new compiler identity.

Measured with the retained candidate (`stage2/x86_64-pc-windows-gnu/simple.exe.rejected`)
and the previously admitted Stage 2 (`d14badc8e34d…`) on the same checkout,
fresh `--cache-dir`, `src/compiler/bootstrap_admission/p2_add.spl`:

| compiler | run | wall | compile phases (last `elapsed_ms`) |
|---|---|---|---|
| admitted d14badc8 | cold cache | 105 s | 9134 |
| new candidate | first run after identity change | 375 s | 8955 |
| new candidate | second run | 103 s | — |

The compile phases are the same (~9 s), so the candidate has no codegen
regression. The ~270 s is a one-time per-compiler-identity cost outside the
phases. Fix direction: run `scv_prime` (`candidate_frontend_admission.shs`)
whenever the journal was produced by a different compiler identity, not only
when the journal is missing. Even warm, 103 s is close to the 180 s budget on
this host.

## 2. Unhinted Windows link flavor falls back to MSVC

`windows_link_flavor_select` (`src/compiler/70.backend/backend/runtime_compiler.spl:53`)
returns `"msvc"` when no ABI-qualified target, `SIMPLE_LINKER_FLAVOR` or
`SIMPLE_WINDOWS_ABI` is present. A plain `native-build` on the default MinGW
clang lane therefore links through `lld-link` and fails:
`could not open 'msvcrt.lib' / 'bcrypt.lib' / ...`. The same fallback makes
`_is_mingw()` false. That sends `_find_c_compiler_windows` to the
clang-cl / cl.exe candidates first, and is plausibly the empty-module
`no C compiler available` ICE in the related bug.

The comment justifies MSVC as "the C compiler's default ABI". On the default
lane the C compiler is llvm-mingw clang (`Target: x86_64-w64-windows-gnu`), so
the fallback should follow the selected C compiler's target, or default to gnu.
Workaround in use: `SIMPLE_WINDOWS_ABI=gnu` (bootstrap lane and
`scripts/check/check-vector-provider-selfhost-apps.shs`). A fix needs a compiler
rebuild.

## 3. Windows link ignores the GNU ABI hint and fails silently

`native_effective_link_os` (`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:195`)
returns `windows-mingw` only for `config.linker_abi == "windows-gnu"` or a
`*-pc-windows-gnu` `config.target_triple`. Neither `SIMPLE_WINDOWS_ABI=gnu` nor
`SIMPLE_NATIVE_BUILD_TARGET=x86_64-pc-windows-gnu` populates those fields for a
plain `native-build`. The trace stays `[LINKER] os=windows`, the link goes
through `link_native_windows_with_engine`, and `link_to_native` returns an error
with no message at all. Measured on the perf probe: 113/113 objects plus 41
runtime objects compiled, link exit 1, no diagnostic, no `perf.exe`.
Expected: the default MinGW clang lane links with the llvm-mingw `clang`
driver (`_link_native_mingw`), and every link failure carries its stderr.

## 4. Further native gaps behind the fixed ones (same diagnostic candidate)

- `pure_database_bitmap_query`: the MIR shard worker crashed with exit
  `0xC0000409`. The cause is a Cranelift verifier panic (`cranelift-codegen/src/verifier/mod.rs:1634`,
  `internal error: entered unreachable code`), i.e. invalid IR from our
  lowering for one module of the closure.
- `http_vector_parser_live_socket`: `E-MONO-032`. `thread_spawn_with_args` at
  `src/lib/nogc_sync_mut/http_server/server.spl:230` gets no inferred type
  arguments from its closure, so the call is not monomorphized.

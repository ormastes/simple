# Target 5 Stage4 hello entry diagnostic (Linux ARM64)

Update (2026-09-29): A current-source exact Stage4 + lld compiler now links
and passes `--version` after the live character-helper and partial-linker
fixes. Its one hello AOT smoke still fails with
`PLUG-E-NOTFOUND: backend=llvm` after MIR/AOP processing. The K1 composition
binding remains the next blocker; no hello size/startup/RSS cohort exists.

Status: BLOCKED for production qualification. This is an investigation of the
standalone compiler entry, not an admitted Stage4 build or a size result.

Worktree: `codex/target5-stage4-sqlite-demand-20260928`, starting at
`27e0e47d653`. The previous current-source dynamic compiler diagnostic checks
hello and runs `--version`, but `--aot` reaches `PLUG-E-NOTFOUND: backend=llvm`.
Its standalone entry never installs the selected K1 backend table. A local
trial called `install_selected_k1_backend_table_v1()` before AOT/JIT; the trial
was removed because ordinary source resolution may bind the in-tree
fail-closed stub instead of the selected composition. Making JIT fail at that
new gate would be a regression. The existing composition-shadowing failure is
tracked in `doc/08_tracking/bug/k1_composition_root_does_not_shadow_stub_2026-09-16.md`.

## Current-source builder results

The pure-Simple Stage2 runtime capsule at
`build/bootstrap-target56/phase2-runtime-capsules/5d71c26b371b83d0041e10b815dae153a38b9f7c61aa0931f3473aaee919e2f6/simple`
was invoked with the `kernel_llvm_cranelift`, compiler, and library source
roots, `--entry-closure`, Cranelift, no stub fallback, and a phase-bound cache.
The compiler entry was `src/compiler/80.driver/main.spl`.

| Requested build | Result |
|---|---|
| Stage4 + `dynamic-runtime` | Capsule rejected the bundle value before build. |
| Stage4 + `simple-core` | 866 source units compiled with zero failures, then Stage4 admission rejected that bundle. |
| Stage4 + `core-c-bootstrap` | Cached 864 units and compiled 2, then the static SQLite provider contract rejected the new `spl_sqlite_provider_abi_version_v1` definition in `runtime_sqlite.o`. |
| Diagnostic without Stage4 admission + `simple-core` | Linked 29,897,584-byte unstripped executable; SHA-256 `37b03ad827bd121bf57fd6230ecc52d0efa59c03c894f9fa668740d9122d89db`. This is a hosted static diagnostic, not Stage4 authority. |

The current `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
also omits `spl_sqlite_provider_abi_version_v1` from
`STAGE4_C_SQLITE_DEFINITIONS`. The symbol is the new demand-load provider ABI
probe, so dropping it to satisfy the old builder would weaken that contract.
The builder and source must use the same provider ABI before this build can be
admitted.

The diagnostic executable with the temporary K1 entry call advanced past
`PLUG-E-NOTFOUND`, but `--aot --O1 --no-debug` on
`test/05_perf/fixtures/interpreter_startup/hello.spl` then failed with
`MIR module has no functions`. The older closed bug
`doc/08_tracking/bug/native_build_mir_module_has_no_functions_2026-07-25.md`
concerned extern/module-level declarations in a different builder and does
not prove this failure is the same issue. No hello executable was produced.

## Gate status and next action

`scripts/check/check-kernel-closure.shs` still reports 2082 classified, zero
unclassified, 3 K0-to-plugin, 7 K1-to-plugin, 9 kernel-to-app/OS, and zero
unresolved edges. The VHDL, worker transport, JIT, and loader imports are
real link-closure work; changing their classifications alone would not remove
them from the binary.

First make the selected K1 composition binding deterministic, then rebuild an
ABI-matched Stage4 authority with the SQLite demand-load symbol in its
provider contract. Diagnose the empty MIR on that authority and produce a
working hello before comparing size, matched C, startup, and RSS. The earlier
14,560-byte LLD hello is a separate one-module core-C diagnostic and cannot
substitute for these gates.

## Continuation: exact SQLite contract repaired

The current bootstrap builder's exact Stage4 SQLite archive contract now
includes `spl_sqlite_provider_abi_version_v1`. This is a required definition,
not an exception to the extra-symbol check. The existing
`test_stage4_cli_c_provider_archives_have_exact_members_and_contracts` test
passed (1 test, 0 failures) against the current provider source. The rebuilt
bootstrap tool SHA-256 is
`1ad11693b36d62a5a3a482df12bafc9c0774b83ffa2e1047495f4954ba2d5189`.
It is a bootstrap tool, not the default compiler authority.

With `SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_COMPILER_ENTRY_STAGE4=1`, the three
current-source roots, Cranelift, and `core-c-bootstrap`, the first Stage4
retry compiled all 866 units with zero failures and passed the SQLite contract.
Linking then stopped because the supplied runtime directory lacked
`deps/libsimple_runtime.a`. A second retry supplied the existing release
staticlib (SHA-256
`b37b597c678c81be955c0f3750539591de285bb6686368634fcd671a522b18cb`)
through that path. It reused 864 units, compiled 2, and advanced to compiler
backfill validation. The new blocker is exact:

```text
compiler backfill source contains runtime/provider ownership outside the manifest:
spl_cranelift_aot_isa_feature_v2, spl_cranelift_aot_opt_level_v2,
spl_cranelift_new_aot_module_config_v2
```

`build_compiler_backfill_archive` derives its export contract only from
`rt_cranelift_*`, while the current compiler archive defines these three
`spl_cranelift_*` AOT configuration functions. The next change must assign
those symbols to the compiler backfill contract and verify its exact closure
and provider disjointness. No Stage4 executable or hello size cohort exists
from these retries. The session stopped after the third focused check/build
cycle as required by the repository iteration cap.

## Continuation: backfill and core-C ownership

The compiler backfill contract now retains the three versioned
`spl_cranelift_*_v2` AOT configuration hooks as exact exports. Its six focused
archive tests pass, including public-export, private-localization,
provider-overlap, and extra-runtime-symbol rejection. The next Stage4 attempt
passed that manifest but rejected overlap with the core-C archive: ordinary
bootstrap core-C still carried `runtime_cranelift_bridge_stub.c`, duplicating
the real `rt_cranelift_*` and versioned `spl_cranelift_*` hooks.

A dedicated Stage4 compiler core-C variant now excludes that stub translation
unit while leaving ordinary bootstrap's named-trap stubs in place. The focused
archive test confirms that the Stage4 variant contains `rt_string_new` and no
`rt_cranelift_*` or `spl_cranelift_*` definitions. A final full current-source
retry compiled 866 units with zero failures and passed both the backfill
manifest and overlap checks. It then stopped at a later exact ownership gate:

```text
Stage4 requested symbols have no archive owner:
rt_execute_native, rt_net_accept, rt_net_bind, rt_net_close, rt_net_init,
rt_net_recv_bytes, rt_net_rx_ready, rt_net_send_bytes, rt_net_socket,
rt_net_stats, rt_net_tx_test, rt_tcp_connect
```

`rt_execute_native` has an implementation in the hosted Rust `native_all`
archive, which is not an admitted Stage4 core-C provider. The network symbols
have Simple extern declarations in `src/lib/nogc_sync_mut/sffi/net.spl` and
bare-metal uses; the current core-C archive does not own them. The next pass
must establish the intended hosted owner or remove these calls from the
compiler entry closure by justified feature boundaries, then prove exact
archive ownership. Import classification or a blanket undefined-symbol waiver
would not supply behavior. The build produced no Stage4 executable or hello
size/startup/RSS cohort. This is the session's third focused fix/check cycle;
no further build retry was made.

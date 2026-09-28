# Target 5 Stage4 hello entry diagnostic (Linux ARM64)

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

# Stage4 bootstrap runtime path conflates link directory and interpreter provider

Status: PARTIAL FIX (Linux ARM64, 2026-09-29). Blocks a fresh Stage4 hello built from
the Target 5 link-capture branch; the saved historical hello is not a substitute.

The pure-Simple Stage2 bootstrap tool at
`simple-target56-completion/build/bootstrap-target56/phase2-runtime-capsules/d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c/simple`
compiled the selected-K1 Stage4 entry closure (866 units, zero source
failures), then rejected `spl_sqlite_provider_abi_version_v1` as an unexpected
definition in `runtime_sqlite.o`. That tool predates the current Stage4 C
SQLite archive contract.

A refreshed Rust bootstrap-only tool from
`simple-target5-native-fix/build/mini_builds/target5_cargo_seed_cache/release/simple`
has the current symbol contract. With the matching static runtime archive
SHA-256 `b37b597c678c81be955c0f3750539591de285bb6686368634fcd671a522b18cb`
in an isolated runtime directory, its first attempt correctly requested
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`. With cold initialization enabled, it
completed 821 source-closure files, then stopped:

```text
warning: failed to initialize runtime provider DynamicPath(".../bootstrap_runtime"):
  ... Is a directory; falling back to static
error: semantic: dynamic SFFI dispatch does not admit argument type 'str'
  without a typed ABI contract
```

`native_loader/src/provider.rs` interprets any nonempty `SIMPLE_RUNTIME_PATH`
as a dynamic library file, while the native-project linker treats the same
value as a directory containing `libsimple_runtime.a` and `deps/` archives.
The bootstrap CLI's `--runtime-path` also sets `SIMPLE_RUNTIME_PATH`, so it
cannot express these two authorities separately. Static fallback did not
admit the text-valued call in this source closure. The generic SFFI rejection
is fail-closed; widening it to accept arbitrary `str` without a typed ABI
contract is not a fix.

Acceptance: expose distinct interpreter-provider and native-link archive
authorities (or choose static interpreter mode for a directory), preserve the
typed SFFI gate, then build the exact current-source Stage4 compiler without
stub fallback. Capture the resulting hello link with
`SIMPLE_NATIVE_LINK_REPRODUCE_PATH`; only then make a matched C size claim.

Evidence logs are retained under
`build/target5-link-reproduce/stage4_build{,_refreshed,_cold}.log` and
`build/target5-link-reproduce/stage4_cache/diagnostics/` in the isolated
`codex/target5-size-attribution-20260929` worktree. They are build artifacts,
not committed release evidence. Three Stage4 build attempts were made this
session; no fourth retry was run.

The native-loader bootstrap provider now treats an existing
`SIMPLE_RUNTIME_PATH` directory as a link-archive location, leaving
`SIMPLE_RUNTIME_LOAD` or the static default to choose interpreter symbols.
An explicit library file path still selects `DynamicPath`. Three focused
native-loader tests pass. The generic dynamic SFFI refusal is unchanged and
now names the function and argument index; 21 focused compiler tests pass.
The refreshed bootstrap-only executable was built with these edits (SHA-256
`bb02dd648769b2dd5ca202a5f88d0fd1a5bd6aed401fc89e0c8892c522c2d3c4`).
Its current-source Stage4 attempt emitted no dynamic-directory provider
warning, but the debug executable reached a 300-second timeout before it
reported a compiler result or the exact foreign call. The process is no
longer live; no Stage4 compiler exists. The next attempt needs an optimized
bootstrap producer or a refreshed pure-Simple Stage2 archive contract, not a
repeat of this debug run. Its log is
`build/target5-link-reproduce/stage4_build_named_sffi.log` in the isolated
worktree.

Optimized bootstrap follow-up: a release-profile bootstrap-only executable
(SHA-256 `640620f7f31cbc66b0656f1d8f247612e847c40db35eda128af9e0f900db2060`)
completed all 821 source-closure files in 22 seconds, then reported
`semantic: unknown extern function: rt_string_substr_from`. The symbol was
already present in native C and Rust runtimes and native codegen's SFFI table,
but was missing from interpreter dispatch. The new handler returns owned text,
counts UTF-8 characters, clamps a negative start to zero, and rejects bad
argument types/counts. Its focused test passed, including dispatch
registration and distinct zero-offset text ownership.

After rebuilding the optimized bootstrap executable, the same Stage4 command
passed that foreign-call site and entered parse. A 300-second bound expired
with 43 of 821 files parsed; the last progress record was
`src/compiler/50.mir/hwir/trap_frontend.spl`. The run reported no later
semantic or link failure, but produced no Stage4 compiler. Logs are
`build/target5-link-reproduce/stage4_release_seed{,_substr}.log`. The current
blocker is the slow bootstrap interpreter parse path on this large closure.
Do not infer a link or size pass from the partial parse. A refreshed pure-Simple
Stage2 archive contract or a measured parse-path improvement is needed before
the current-source Stage4 compiler and hello capture can be completed.

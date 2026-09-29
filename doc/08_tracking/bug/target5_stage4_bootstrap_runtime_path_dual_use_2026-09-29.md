# Stage4 bootstrap runtime path conflates link directory and interpreter provider

Status: OPEN (Linux ARM64, 2026-09-29). Blocks a fresh Stage4 hello built from
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

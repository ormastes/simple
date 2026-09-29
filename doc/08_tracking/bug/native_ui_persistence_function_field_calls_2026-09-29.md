# Native persistence callback fields emitted as method calls

## Observed defect

The retained strict Windows CLI link at source `61c95134bd4c3e57d9e046b85aca6ca99ec1e953` failed with `UiAccessPersistence.list_events_fn` and `UiAccessPersistence.query_nodes_fn` undefined. `mod_2286.o` referenced them from `UISession.access_persisted_events` and `UISession.access_search_nodes`. The actual persistence owner declares these as function-valued fields, not methods (`src/lib/nogc_sync_mut/ui/session.spl:48–49`). Its existing insert/snapshot paths already load callback fields into locals to avoid this lowering ambiguity.

Evidence is retained in `D:/dev/simple-windows-reviewed-bootstrap-20260929/61c95134bd4c-attempt2/retained-modules.symbols.txt` and the frozen checkout's `build/bootstrap/win-61c95134bd4c-2/windows/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log` (undefined-symbol entries897/900). The ordinary-symbol audit documents the independent Windows module-retention issue; this leaf change does not claim to repair all CLI link failures.

## Scoped correction

Load `list_events_fn` and `query_nodes_fn` into local values before calling them. Preserve each nil guard, every argument, and the callback's `Result` without translation. This is an explicit workaround for a compiler defect: native dotted calls on function-valued fields should lower to indirect calls after field-type resolution. The compact dotted form remains a compiler follow-up, not a syntax rule to normalize silently.

The same scoped patch corrects the watcher client's two obsolete `ShbReader.read_full_interface` calls to the real `read_all() -> ShbModuleInterface` API. The surrounding watcher-request `Result` match and empty-interface fallback are preserved.

## Regression and status

- `test/01_unit/app/ui/session_access_persistence_port_spec.spl` uses the actual `UISession` and callback class, captured callback payloads, all query arguments, exact errors, action/snapshot side effects, and both missing-port guards. It replaces the obsolete trait-shaped probe.
- `test/02_integration/watcher/watcher_shb_client_cache_spec.spl` exercises real SHB writing/reading and the production watcher client: sentinel fresh-cache sections, missing-cache generation and reread, and missing-source fallback. The generation case first parses its source using the existing parser/AST owners, satisfying the SHB extractor's current parsed-arena precondition. It does not simulate the reader/cache implementation.

Prepared on GitHub main `5e36e64c1b26642fb43978f709b03eb9a975b9fe` in the isolated `work/bootstrap-shb-ui-callers-20260929` branch. **Execution pending root review and a trustworthy admitted producer.** No native, Phase2 matrix, or bootstrap phase PASS is claimed. The daemon-request-success branch is corrected by the same API substitution but is not exercised by the filesystem regression; a daemon transport integration remains separate.

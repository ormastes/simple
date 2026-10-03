# Rust seed full-scan native build leaves OS branches unprocessed

- **Filed:** 2026-10-02
- **Status:** OPEN; source-path audit, full-scan reproduction pending.
- **Scope:** Rust seed `native-build` without `--entry-closure`.

The entry-closure discovery path preprocesses module-level `@when(os="windows"):` / `@else:` / `@end` before the Rust seed parser sees imported files. The full-scan path does not. `NativeProjectBuilder::discover_files()` selects `discover_files_full_scan()` when `entry_closure` is false (`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs`). `NativeProjectBuilder` then reads each file and pushes its raw source into `file_sources` without OS-branch preprocessing (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`, near the discovery step). The Rust parser treats `@when` as a function decorator and rejects its trailing colon.

The release tree contains `@when(os="windows"):` in `src/lib/nogc_sync_mut/io/windows_redirected_process.spl` and `windows_resource_owner.spl`. A full-scan seed build that includes `src/lib`, such as `src/compiler_rust/target/bootstrap/simple native-build --source src/lib --backend=cranelift -o <output>` without `--entry-closure`, is therefore expected to encounter the same parse shape. This is an inference from the source paths; no full-scan reproduction was run in the bounded Stage 2 session.

Draft PR #2221 deliberately repairs the entry-closure path needed for Stage 2. A follow-up should share the same target-aware preprocessing at full-scan source ingestion, test both Linux fallback and Windows body selection, and verify a full-scan native build. Preserve malformed-directive failure and diagnostic line numbers.

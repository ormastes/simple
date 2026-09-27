# Simple MCP redeploy and compiler blockers

**Date:** 2026-09-26
**Status:** Open, Simple MCP redeployed; full CLI link and LSP verification blocked
**Scope:** `src/app/mcp/main.spl` native build and current-source redeploy

## Observed evidence

The isolated build in `/tmp/simple-mcp-deploy` uses source whose
`src/app/mcp/main.spl` SHA-256 matches this worktree
(`1f14c67a1d79150a56e1328f6acd0abc0852f817185217d465aead9244dc0816`).
Its command uses `--source src/compiler --source src/app --source src/lib
--entry-closure --entry src/app/mcp/main.spl` and a private cache. The
deployed binary at `bin/release/aarch64-unknown-linux-gnu/simple_mcp_server`
is dated 2026-09-06 and is not a current-source artifact.

The build log `/tmp/mcp-build-simple.log` records:

- Attempt 1: `native module name collision after path sanitization` between
  `build/scv/snapshots/<revision>/src/app/mcp/main_lazy_json.spl` and
  `src/app/mcp/main_lazy_json.spl`, both mapped to
  `app.mcp.main_lazy_json`.
- Attempts 2 through 4: `SCV-E-ADMISSION: filesystem-event-journal-missing`,
  despite `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
- Attempt 5 remained CPU active on 2026-09-26 with no native output yet. The
  process handle was PID 2372519. Do not infer success or a terminal failure
  from the quiet log while that handle is live.

The collision is detected by
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` during
entry-closure source discovery. The duplicate paths show the SCV snapshot and
live source were both selected; the exact selection error has not been proved.

## Fresh bootstrap attempt

A separate checkout at `/tmp/simple-mcp-redeploy-fresh` used
`SIMPLE_NO_STUB_FALLBACK=1` and the strict Cranelift Stage 2 bootstrap. The
first build found a source HIR inference error in
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`: the untyped
`match` receipt was inferred as `Nil`. The isolated source checked provider
admission inside the `Ok` arm. Current upstream main instead uses an explicit
`ParserProviderAdmissionV1` annotation, so this PR keeps that version and
updates the stale source-shape test. With the isolated change, Stage 2 compiled
3 files, reused 898 cached files, and linked its CLI without compile failures.

The Stage 2 admission smoke still rejected that CLI. Its first three frontend
fixtures passed (`p2_add`, MIR retention, and module path naming), then the
positional `hello_world.spl` native build exited 132 while parsing the single
source file. The bootstrap removed the rejected binary. This result repeated
after both source rewrites, so the three-cycle verification limit is reached.
The retained evidence is in
`/tmp/simple-mcp-redeploy-fresh/build/mini_builds/mcp_redeploy_stage2_retry2.log`
and its `stage2-sanity.env.frontend-bootstrap-0.status.env` receipt under
`.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/`.

At this point no current-source MCP or LSP MCP binary was admitted or deployed
from this checkout. The production wrappers still used their prior binaries.

## Crash diagnosis after the strict retry

The rejected Stage 2 binary was rebuilt once into an isolated diagnostic path
with the preserved native cache. GDB located the exit-132 trap in
`current_core_lexer_save`: with `lex_env_save_enabled[0] == false`, its bare
`return` compiled to an AArch64 `udf` instruction. The source now guards the
environment writes with `if lex_env_save_enabled[0]` and falls through normally.
The rebuilt candidate passed parsing of the positional hello-world fixture.

The next default-cache run then exited 139 in
`compiler.hir.generated.hir_codec.hc_enc_scope_id`, called by
`hir_cache_store`. The `ScopeId` argument at the fault was `0x2000000002`,
which the generated code treated as a pointer. With `SIMPLE_HIR_CACHE=0`, HIR
lowering completed but the same candidate exited 139 later in
`mir_provider_function_name` while reading a `HirFunction` field. These are
separate current blockers for the pure-Simple Stage 2 frontend admission;
disabling HIR cache alone does not admit the build. GDB logs and the retained
candidate are under `/tmp/simple-mcp-redeploy-fresh/build/mini_builds/`.
At the MIR fault, the function value was tagged `0x1` (nil). The caller is
`MirLowering.lower_module`, which iterates `module.functions.values()` and
passes each typed `HirFunction` to `register_provider_callable_link`; the
reason that value became nil remains unproven. A separate codec fault shows
`ScopeId` value `0x2000000002` being dereferenced as a pointer. Neither fault
has been bypassed or accepted for deployment.

An isolated source experiment replaced the first
`module.functions.values()` loop in `MirLowering.lower_module` with typed
key-based dictionary reads, matching existing compiler code. The same
`mir_provider_function_name` fault persisted. The experiment was reverted in
the isolated checkout and was never copied into the main worktree. With
`SIMPLE_INTERP_TRACE=1`, the driver reports the `bootstrap_entry` HIR branch,
zero lowering errors, and completion of HIR and monomorphization before the
MIR fault. The currently installed `llvm-config` is 23.1.0; bootstrap requires
exactly 23.1.1, so switching backend is not an admitted route on this host.

## Older admitted pure-Simple producer route

The retained Stage 2 executable at
`build/mini_builds/transient_name_owner/stage2-rebuild/admitted/simple` has a
stage-2 admission receipt and SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
It is an older pure-Simple bootstrap compiler, not the current Rust seed. Its
Cranelift backend failed a current-source hello-world native build at object
path resolution; its LLVM backend built and ran that fixture successfully.
This producer uses LLVM 23.1.0 directly, outside the strict bootstrap script's
23.1.1 admission gate, so its provenance is narrower than a newly admitted
current-source compiler.

With `SIMPLE_NO_STUB_FALLBACK=1`, that producer built the tracked-source Simple
MCP entry from the isolated checkout. The candidate linked 115 files, exposed
176 tools with `SIMPLE_MCP_TOOL_SET=all` (all 167 previously deployed names plus
9 Caret tools), and passed initialize, tools/list, and a `simple_search` call.
It was deployed to `bin/release/aarch64-unknown-linux-gnu/simple_mcp_server`
with SHA-256 `381bc3a1cfb41fc3d28f07187766590a206efb5ebd226b4ce1b97ee2b63bc8e4`.
The production wrapper re-probed it and passed the same live calls. The old
binary and sidecar are retained under
`/tmp/simple-mcp-redeploy-fresh/build/mini_builds/predeploy_simple_mcp_server*`.

The same producer built an LSP MCP candidate with 13 tools. Its production
wrapper accepted the candidate under a temporary override, but a real
`lsp_symbols` call needs a full pure-Simple CLI, which is absent in the isolated
checkout. The first full-CLI LLVM build attempt timed out after 600 seconds
while CPU active. A second attempt reused the cache and reached linking, but
the requested `core-c-bootstrap` runtime bundle is too narrow for the full
entry: mold reported missing Cranelift, GPU, SQLite, CLI, and owner symbols.
The build log is
`/tmp/simple-mcp-redeploy-fresh/build/mini_builds/current_full_cli_llvm_retry.log`.
The retained 2,416 compiled objects were also linked diagnostically against
the fresh `libsimple_native_all.a`; 484 unique symbols remained unresolved,
including pure-Simple module calls. The evidence is in
`/tmp/simple-mcp-redeploy-fresh/build/mini_builds/current_full_cli_manual_link.log`.
The full CLI requires a matching full runtime bundle **and** complete source
closure; changing the runtime archive alone cannot admit it. No LSP binary was
deployed from this candidate yet.

The required `check-mcp-native-smoke.shs` was attempted once with the older
admitted pure-Simple bootstrap compiler as `SIMPLE_BINARY`. It stopped at its
first `run` dependency with `error: unknown command 'run'`; that Stage 2
compiler supports `native-build` but is not a full CLI. The smoke gate remains
unverified, and the Rust seed was not substituted for it.

The deployed MCP binary's sidecar records its final release path and passes
`sha256sum -c`. The production wrapper had already verified the same hash and
passed initialize, tools/list, and `simple_search` after deployment.

## Acceptance for the redeploy

1. Reproduce and fix the duplicate source selection and journal admission in
   an isolated build lineage. Preserve its cache and do not modify the
   unrelated live build process.
2. Build MCP and LSP MCP from the current source with admitted compiler
   provenance and `SIMPLE_NO_STUB_FALLBACK=1`.
3. Deploy hash-admitted binaries to `bin/release/<host-triple>/`, then pass
   live initialize, tools/list, and representative tools/call probes through
   the production wrappers.
4. Run the repository's MCP native smoke and relevant source checks before
   declaring the redeploy complete.

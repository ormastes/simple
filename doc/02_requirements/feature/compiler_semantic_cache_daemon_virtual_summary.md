<!-- codex-requirements -->

# Compiler semantic cache manager, virtual summary, and lazy startup requirements

Selected bundle: Feature B, S1, D1, A1, V1, L1, C1, and NFR Option 2.

## Cache authority and snapshots

- **REQ-CSM-001:** The compiler shall freeze a coherent multi-file `CompileSnapshotV1` from same-handle source reads plus pre/post validation of ordered resolution candidates, negative candidates, anchored directory generations, symlink policy, case/Unicode policy, generated inputs, configuration and provider/toolchain identity.
- **REQ-CSM-002:** A mutation detected before snapshot publication shall cause one bounded restart; a second mutation shall fail with `source_snapshot_unstable`. After publication, compilation shall use only frozen bytes and shall never mix generations.
- **REQ-CSM-003:** `SourceBlobV1`, `FileAstV1`, `PublicSummaryV1`, `SemanticReadSetV1`, snapshot trees and action manifests shall be immutable, domain-separated, schema-versioned CAS objects verified by size, magic and digest.
- **REQ-CSM-004:** Absolute worktree paths, branch names, inode values, mtimes and database row IDs shall not define artifact identity. Logical repository-relative paths may enter identity only when language semantics require them; presentation paths remain separate.
- **REQ-CSM-005:** Identical complete action inputs across worktrees and branches shall reuse the same verified objects. Any source, resolution witness, trait/AOP/macro input, target/layout/feature, compiler owner, provider byte/configuration, runtime or linker identity change shall miss.
- **REQ-CSM-006:** Declared hermetic compile-time inputs shall be hashed before execution. Supported deterministic providers may supply replayable values plus provider identity. Undeclared environment, clock, randomness, network, filesystem or process reads shall make the action uncacheable and prohibit successful action-receipt publication.

## Catalog, journal, daemon, and GC

- **REQ-CSM-007:** PureDatabase shall store rebuildable projections for aliases, derived objects, roots, leases, access metadata, tombstones and quarantine. It shall not be the sole authority for immutable objects or admitted action/root mappings.
- **REQ-CSM-008:** Admitted action/root authority shall use a checksummed append-only journal naming rooted CAS manifests. Checkpoint shall publish and verify a canonical CAS snapshot, atomically advance a two-generation superblock, and only then make old segments eligible for lease-aware GC.
- **REQ-CSM-009:** A per-user cache daemon shall auto-start through credentialed single-instance admission, private socket/cache permissions, protocol/schema handshake, writer epoch and readiness receipt resistant to stale PID reuse.
- **REQ-CSM-010:** After one bounded reconnect/restart attempt, the client shall compile in process. Without exclusive writer ownership it may read verified CAS values but shall write only to an isolated spool reconciled by the next admitted owner. Daemon and fallback paths shall produce identical bytes and diagnostics.
- **REQ-CSM-011:** The daemon shall exit 10–12 seconds after the final request, lease, publication and GC transaction. In-flight work shall prevent idle exit.
- **REQ-CSM-012:** GC shall mark active build/snapshot leases, admitted journal roots and explicit pins; quarantine corruption; and use tombstone/two-generation deletion so concurrent readers cannot lose live objects. Catalog reconstruction from journal/CAS shall be supported.
- **REQ-CSM-012A:** Every host shall use one configured physical cache root containing the database, CAS, journal, spool and quarantine trees. The common environment/path facade shall expose `get_user_local_dir` and `get_cache_location`; the latter uses `SIMPLE_CACHE` when it names an absolute root, otherwise the platform cache directory plus `simple/cache-manager`. This host overrides it with `/mnt/data/simple-cache-manager`; Windows therefore defaults to `%LOCALAPPDATA%\simple\cache-manager`, Linux honors `XDG_CACHE_HOME` before `~/.cache`, and macOS uses `~/Library/Caches`. Physical-root spelling never enters semantic identity.

## Virtual summary and AST reuse

- **REQ-CSM-013:** `_tldr.spl` shall be a deterministic, grammar-valid public-summary projection with source/snapshot/schema/compiler provenance. It shall emit canonical bodyless forward declarations before dependent public surfaces, using deterministic dependency-SCC/topological order with stable-symbol tie-breaking, then public declarations, layouts/ABI, traits/impl/coherence facts, extensions, reexports, AOP selector metadata/order, macro signatures/read sets and references to required generic/inline/const bodies. Missing, conflicting or signature-mismatched required forward declarations shall fail closed.
- **REQ-CSM-014:** Virtual summaries shall use `simple-summary://<snapshot>/<logical-path>/_tldr.spl`, never shadow real files, never participate in source import resolution and expose no private AST by default.
- **REQ-CSM-015:** The Simple compiler/CLI, MCP, LSP MCP and SPipe shall consume one shared `VirtualSourceStoreV1` facade backed by `SummaryStoreV1`; no consumer may reparse source or implement a parallel summary generator. The facade shall support bounded list/stat/read/page operations over the exact frozen snapshot. Authorization shall bind root, session, capability, snapshot, path, visibility, limit and token expiry; generated/untrusted provenance shall be explicit for LLM consumers.
- **REQ-CSM-016:** AST reuse shall use stable indices only, validate all counts/offsets/depth/string bounds and compiler/schema/source identity, and match fresh parse semantics and code generation on admitted Phase 2 and Phase 3 runtimes.
- **REQ-CSM-017:** Imported unchanged modules shall load validated summaries rather than private bodies. Generic, inline, CTFE/macro, selected trait implementation and selected AOP advice bodies shall load lazily by immutable digest when required.

## MDSOC startup capsules

- **REQ-CSM-018:** The eager capsule shall contain only argv/configuration, encoding, diagnostics, anchored path/hash/snapshot admission, public signature/import scanning, resolver/type/trait/AOP summary contracts, loader/interpreter interfaces and typed provider/capsule manifests.
- **REQ-CSM-019:** Interpreter execution bodies, loader mapping/JIT/resource bodies, AOP implementation, monomorphization, MIR, borrow checking, optimization, concrete backends, object/archive/link owners and optional tools shall be separate admitted virtual capsules loaded only for the selected task.
- **REQ-CSM-020:** The eager `src/lib` closure shall be limited to core text/bytes/collections/result/diagnostics, encoding, argv/config facade, anchored file/path access, hashing, bounded collections and admission interfaces. Database, daemon transport, network, UI/web/GPU/audio, tests, reporting and process-heavy helpers shall be task capsules.
- **REQ-CSM-021:** Provider/capsule admission shall bind content digest, ABI, capabilities, configuration and effect/read-set contract before activation. The previous generation shall remain authoritative until the candidate is admitted.
- **REQ-CSM-022:** Closure gates shall prohibit concrete backends, linker/archive, AOP implementation, MCP/LSP/test/UI and unrelated product commands from `--help`, cache-hit query and frontend-only startup.
- **REQ-CSM-022A:** Logical cache paths shall use canonical UTF-8 `/` separators on every host. A host path authority shall normalize or reject Windows drive, UNC and extended-length prefixes, backslashes, case aliases, reserved device names, alternate data streams, trailing dots/spaces, symlinks and junctions before anchored access; neither `C:\...` nor a physical `/...` path may become a logical cache key.

## Safety and staged activation

- **REQ-CSM-023:** Cache reuse shall remain shadow-only until fresh-versus-hit AST/summary/object bytes and diagnostics match across the complete mutation, corruption, crash, concurrency and cross-worktree matrices.
- **REQ-CSM-024:** Same-action/different-output results shall be quarantined as nondeterminism. Corrupt, forged, truncated, oversized, symlinked or wrong-schema objects and receipts shall fail closed.
- **REQ-CSM-025:** No authoritative HIR/object hit or cross-phase reuse shall activate until admitted pure-Simple Phase 2 and Phase 3 bootstrap parity proves the complete action/read-set model.

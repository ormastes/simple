# Item 6 stable workspace root generation (2026-10-10)

Status: focused native helper PASS; production invalidation and performance qualification pending.

The release baseline `e905cd1b32ec290e1966a28c09b5ddb31ba1f61b` passed
`snapshot.tree_id` as `PackageModuleIndexBuildAuthorityV1.root_generation`.
SCV derives that tree ID from the complete inventory digest, so any source edit
changed the root generation. The warm route conservatively invalidates all
changed modules when old and new root generations differ. That prevented the
per-module transition from applying even when one private body changed.

The cold producer now receives the source root that the manager admitted with
the SCV snapshot and derives a stable, domain-separated workspace root digest.
The snapshot revision, commit, tree, and inventory digests remain separately
bound to each new generation. The first transition from the old tree-based root
remains conservative; later generations in the same workspace can reach the
exact per-module comparison. Distinct source roots receive distinct root
digests. This is an identity correction, not a measured speedup.

A no-stub native probe built with the historical pure-Simple Stage 2 compiler
SHA-256 `319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
The final build compiled 1 source, reused 6 cached units, failed 0, and linked
an 81,600-byte probe SHA-256
`c14fa2ca0d5375d9ed5961eda667c6fab4871f9de152bf9752b0552aad49a900`.
The executable exited 0 with `PASS cold_full_index_root_identity_probe`.
The first attempt lacked the core C runtime in the sparse checkout; the next
attempt hit the tool's 10-second foreground limit. The third used the same
source with a bounded detached build and the core C bundle.

This probe covers the pure root identity function. It does not compile the
full production cold publisher, execute a prior/new generation transition,
prove absence of unrelated recompilation, or provide paired time/RSS evidence.
Those gates, along with the 44-scenario acceptance contract and current-release
compiler admission, remain open.

A bounded attempt to build the production package-index acceptance owner from
this release checkout did not produce an executable. The first attempt used a
sparse library projection and reported unresolved imports; after expanding
`src/lib` and `src/app`, the historical Stage 2 compiler stopped during
discovery at `src/lib/nogc_sync_mut/io/windows_image_owner.spl:34:20`
(`expected Fn, found Colon`). A final bounded attempt omitted the
explicit `src/lib` source root while keeping the project stdlib on disk;
discovery stopped at the same syntax. This is a tool/source compatibility
blocker, not an acceptance failure or evidence about the new root identity.
The three build attempts have exhausted this session’s fix/verify limit.

The current acceptance owner has a separate product-scope gap.
`test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`
calls `private-body-export-early-cutoff` without `--scope owner`, but
`src/app/test/package_index_acceptance.spl` returns status 3 with
`acceptance_status=incomplete` and names source-derived classification,
compiler completion, and production filesystem observations as missing.
The production route already has per-module comparison logic, but a compiled
owner alone cannot satisfy this system scenario. It needs an actual edited
source, new index publication, exact dirty-package execution, and observed
time/RSS and file-read counters before this gate can pass.

The warm driver reads `SIMPLE_PACKAGE_INDEX_CHANGED_MODULES` in
`driver_source_pipeline_loading.spl`. A tracked source/script/test search
found no in-tree producer for that environment key; the grouped runner
explicitly excludes it from inherited environment. Thus the stable root
identity only removes one conservative fallback. An automatic source edit
still needs an admitted event-to-module mapping (or equivalent source-derived
old/new generation comparison) before exact warm invalidation is reachable
without an external caller supplying hints. Empty hints currently select
the no-op route.

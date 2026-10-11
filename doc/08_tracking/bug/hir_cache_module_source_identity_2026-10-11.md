# HIR cache aliases byte-identical configured module owners

Status: source repair drafted; native producer rebuild and regression execution pending.

The admitted Phase 2 compiler `48975d35845f703116db796224c4c8cc13a8aa68dc0395664881f8594096fa6d`
crashed while building the genuine subsystem test generator with both LLVM and
Cranelift. The LLVM worker exited on SIGSEGV; the enclosing process returned
117. Peak process-tree RSS was 3,820,392 KiB, below the enforced 6,835,937 KiB
limit. No native test executable or test PASS resulted.

The retained core identifies `capture_cold_hir_typed_receipts_v1` at offset
8068. Its error-reporting branch indexes `Dict<text, HirModule>` with integer
zero, receives tagged nil, and dereferences address 8. This masks the original
`cold-hir-module-source-mismatch` rejection.

Inspection of all 201 source-owner paths and 103 HIR modules found one identity
mismatch: `lib.nogc_sync_mut.env.mod` owns `src/lib/nogc_sync_mut/env/mod.spl`,
but its cached HIR path names `src/lib/nogc_async_mut/env/mod.spl`. Both files
have SHA-256 `83bea209d4c2355aa67b8b445355043fb5225d68e9e64d9bc606d4c7cab84c8f`.
The HIR cache key includes content, closure, entry status, environment and codec,
but omits the source identity retained in serialized HIR.

The repair adds a versioned, fixed-width SHA-256 of the exact source path to the
cache key. Existing entries remain on disk but cannot match the new keys. The
diagnostic resolves the source owner's module name and checks dictionary
membership before reading its path. The strict cold receipt identity check is
unchanged; configured sync/async owners remain separate.

`hir_cache_source_identity_spec.spl` exercises same-content distinct paths,
same-path stability, source edits, closure changes and entry status. It has not
executed successfully: the admitted compiler has no generic `run` command, and
the obsolete executable in the canonical release path rejects current source
syntax before running cases. Static review is not an executable PASS.

The supported `SIMPLE_HIR_CACHE=0` switch permits a separate configuration-only
native attempt without weakening receipt checks. That attempt advanced past
cold receipt capture and monomorphization into MIR lowering, confirming the
cache boundary; its remaining compilation/result status is separate evidence.

Session evidence: `/home/yoon/dev/phase2-six-results-20261011/llvm-generator-crash/`
contains the core, backtrace, fault disassembly and `hir-path-mismatch.txt`.
The original failing product and cache are retained under
`llvm-interpreter-current/`; the changed configuration uses the isolated
`llvm-interpreter-nohir-001/` output root. Neither is a full product PASS.

# Phase 1 lowering owner imports (2026-10-11)

Status: source repair prepared; runtime qualification remains OPEN.

## Retained cause and existing production contract

The retained component ledger contains 12 `MirLowering` undefined-variable
signatures and 12 `HirLowering.lower_module` owner-import candidates selected by
the exact signature classifier. These are distinct import failures, not evidence
that lowering itself produces correct output after import resolution.

`src/compiler/50.mir/__init__.spl` documents that `MirLowering` and `MirError`
remain reachable through direct submodule imports. The existing production
driver imports `compiler.mir.mir_lowering.{MirLowering}`. Release commit
`57cf0e58a7b` already applies that contract to the remote RV32 compiler; its
retained failure row is therefore already source-repaired and is excluded from
this change. Eleven remaining specs use `MirLowering.new` while importing only
the broad MIR facade. Each gains the same direct owner import.

`HirLowering` lives in `compiler.hir.hir_lowering.types`, but its `lower_module`
implementation lives in `_Items/module_lowering.spl`, exported by `items.spl`.
Twelve retained specs import the type but omit that implementation surface.
Each gains `use compiler.hir.hir_lowering.items.*`. This also includes the
`module_callable_types` implementation needed by the nil-safe return scan spec.

Twenty-three specs each receive one import line. All non-import source lines,
including every assertion and helper body, are unchanged. Production source and
executable scenario counts are unchanged. Existing manuals retain the same
scenarios and assertion descriptions.

## Bounded diagnostic evidence

Evidence root: `build/phase1-lowering-surface-20261011/` in the owning workspace.
`family.json` records all 24 selected retained rows, signatures, source hashes,
the 23 additive repairs, and OPEN/NOT_PROVEN qualification states.

The immutable cached Rust Stage 1 producer has SHA256
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
The bounded collector has SHA256
`6e7d07e3f42ae203f6ad8086122f3aecf4e90ed3b093c7af45017e1461601cdc`.
Each launch has a 45-second timeout, 1 GiB process-job RSS cap, 1 MiB log cap,
3 GiB disk floor, and 64 MiB artifact-growth cap. All jobs ended with zero active
processes; no compiler rebuild occurred.

| Diagnostic | Result | Peak job RSS (KiB) |
|---|---|---:|
| MIR public-facade constructor baseline | 0/1; MirLowering undefined | 113228 |
| Experimental facade type re-export | 0/1; same error; edit discarded | 111828 |
| MIR direct owner import | 1/1 provisional PASS | 858312 |
| Original module_filename_populated spec | 0/2; missing lower_module | 404440 |
| Repaired module_filename_populated spec | 2/2 provisional PASS | 588456 |

MIR used three cycles and must not be replayed. HIR used two cycles; its green
confirmation must not be replayed. The MIR ephemeral source lived under the
owning workspace's build tree. The HIR baseline and repaired sources lived
inside the isolated release worktree. `SIMPLE_LIB`, cwd, and project-root
overrides requested the isolated release source, but the diagnostic emitted
some std-source paths from `C:/dev/simple`. This resolver binding has not been
fully admitted. These receipts prove the observed diagnostic behavior only.
They do not qualify all 23 specs, their entire dependency closure, or release.

## Concrete performance debt

The single MIR constructor case reached 858312 KiB (about 838 MiB) in the
diagnostic process job, versus 113228 KiB before resolving the owner import.
The HIR two-case confirmation reached 588456 KiB. Full import closure loading
is a concrete cached-bootstrap memory cost, even for tiny assertions. Preserve
the receipts as a bounded import/RSS bug reproducer; investigate dependency
loading/cache behavior with an admitted pure runtime before broad execution.
These numbers do not establish pure-runtime performance or a production NFR
pass. No rebuild or additional MIR retry is authorized by this evidence.

## Outstanding admission

The remaining 22 repaired specs have not been executed by this lane. Subsequent
assertion failures, undefined helpers, and host failures remain independent.
Required admitted pure-runtime core/lib/MCP/LSP checks and smoke gates are not
available, so this grouped change remains a draft and has no release PASS claim.

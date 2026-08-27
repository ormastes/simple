# MIR Coverage V1 Inventory Foundation

This executable unit specification freezes the standalone data boundary used
by later MIR coverage lowering. It does not add MIR instructions, runtime
counters, optimization behavior, or backend emission.

## Contract

`MirCoverageModeV1` distinguishes disabled, decision-only, and
decision-plus-condition compilation. A coverage site is identified by:

- canonical repository-relative authored source path;
- exact SHA-256 identity of the bound source text;
- canonical function name;
- nonempty byte span, positive line and column, and source-preorder occurrence;
- typed `if`, `while`, `and`, or `or` site kind;
- exact SHA-256 identity of the text inside the declared span.

The finalizer-facing renderer validates every source and site before emitting
the runtime test runner's existing SDN decision/condition table grammar. The
SHA-256 decision site ID remains the stable semantic identity. A condition's
semantic ID commits both its canonical site and its intended parent decision
semantic ID, so a nested condition cannot be reparented to another containing
decision while preserving identity. After sorting canonical
site keys, the renderer separately assigns deterministic, nonzero decimal IDs
within the runtime probe ABI's `u32` range. It emits only zero counts and
rejects duplicate keys or conditions whose parent is outside the finalized
decision inventory. A condition must also share its parent's authored source,
source identity, and canonical function, and its span must be contained by the
decision span.

`mir_coverage_finalize_v1` turns the complete closure inventory into an
immutable `MirCoverageCatalogV1` sideband. It sorts all module inputs together,
assigns closure-global runtime IDs, retains semantic IDs, zero-count SDN, SDN
SHA-256, and catalog SHA-256, and replaces source bodies with path/hash
identities. Disabled mode returns an empty nonpublishable catalog. Because this
standalone stage has no MIR probe-emission capability, the publication guard
always fails closed with `MIRCOV-E-PROBES-ABSENT`.

## Executable scenarios

The mirrored spec verifies:

1. input order cannot change the rendered manifest;
2. disabled mode emits no residual manifest;
3. enabled modes emit only zero-count rows;
4. absolute, traversal, ambiguous, Windows-style, and delimiter-injected paths
   fail closed;
5. malformed or mismatched source hashes fail closed;
6. duplicate source, decision, and condition identities fail closed;
7. empty, negative, oversized, and out-of-source spans fail closed;
8. an anchor hash must match the exact bound source span;
9. missing or conflicting source bindings fail closed;
10. wrong site kinds, orphan conditions, empty enabled inventories, and mode
    conflicts fail closed;
11. zero-count SDN contains deterministic decimal runtime IDs and is accepted
    by the runtime manifest parser while semantic SHA identities remain intact;
12. cross-source, cross-function, and out-of-decision-span conditions fail
    closed;
13. cross-module input permutations produce the same closure catalog and IDs;
14. finalized catalogs retain source identities but no source text;
15. duplicate closure inputs fail before catalog construction;
16. disabled mode produces an empty nonpublishable catalog; and
17. enabled catalogs remain nonpublishable while probe emission is absent; and
18. nested condition identities differ when their intended parent differs.

## Deferred integration

Opcode definition, HIR-to-MIR lowering, probe insertion, optimization
preservation, native backend emission, and qualification-run integration are
separate changes. Those phases must consume this V1 identity and runtime-ID
allocation boundary rather than reconstructing identities from observed
runtime coverage. A later probe-emission owner must replace the V1 publication
guard with a capability-bound proof; constructing a catalog is not publication
authority.

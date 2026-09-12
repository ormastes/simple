# G candidate integration — 2026-09-11

Status: committed integration candidate, **production completion not established**.
The outstanding list includes missing implementation as well as qualified
verification. No release, push, performance admission or measured coverage is claimed.

## Baseline, ownership and order

The isolated branch `codex/g-production-integration-20260911` starts at
`bb1b9cab706e58ef9d2067a1064937656733f015` (`origin/main` at integration start).
The worktree is `/tmp/simple-g-production-integration-20260911`. Shared main and
all source candidate worktrees were preserved, including their dirty paths.

| Group | Source candidates | Integrated sequence/end |
|---|---|---|
| G0 | Documentation recovery head `ca5453cca75` | Retained separately; its broad recovery/skill changes are not silently overlaid onto newer main documentation |
| G1 | `e12dd574c00` through `4a23b7711ea` | `2b680a58664` through `940684b3d5a`; later imports/manuals `995f983a5a2` |
| G2 | `b6a3cd5f37f`, `474e1be8f79`, `1c9a307c587`, `6e3e914558d` | `fce5db8e2b3`, `a6e9c951ea9`, `f872b5f5213`, `3df66123366` |
| G3 | `071b00aa962` through `e5f30f5ece5` | `e642c6ce0b1` through `6572d782fb3`; retained-history correction `ce6d993223c` |
| G4 | `ac72d462783`, `f8b65b7c372`, `f68c697b542`, `4298b86d5cf`, `53e6af40627` | `dc30c6d2c28` through `ebf6280b7ea`; integrated preflight tests `7f94da1b8ea` |
| G6 | `0c82007566f`, `0fe967551c5`, `f647796dfbf`, `ca11542652c`, `48e6027513f` | `95158cae304` through `17fed14ef16`; successor test/manual merge `517f56b6045` |
| G5 | `f786e95c573`, `0588b459550`, `428c771b4ac` plus exact successor dirty boundary hunks | `c05b014a23a`, `adba488088b`, `d8930516e0b`; common/host/facade integration `44a70925e6d` |

G4's final source candidate already contains the namespace/reopen/context test
successor coverage represented by `3032e9cbd5c`, `a6579e2daa9`, and
`15dce82497f`. G6's semantic/header/profile accounting corrections are applied
in dependency order. Shared environment-provider ownership remains with E;
G2 intentionally retains `6e3e914558d`'s shared-provider-contract exclusion.

## Conflict ledger and corrections

One add/add conflict occurred in
`src/compiler/80.driver/cache/publication/three_payload_selected_head_publisher.spl`.
The G4 version replaces the G3 provisional revision/generation/manifest fields
with explicit prior revision/generation and target generation/manifest fields.
It additionally verifies accepted-prefix length/digest and exact journal
operation/sequence. The obsolete closed publisher wrapper had no callers in
the integrated source/test tree and was removed with G4's replacement.

The stale selected-head unit spec only failed because G3 was absent. It now
uses a shared real canonical packet fixture and checks coherent preflight,
negative prior/target identity, prefix bounds/digests, sequence mismatch, and
later unselected journal bytes. These tests cover logical validation; they do
not manufacture a physical namespace receipt. Explicit `std.spec.step` imports
were added to the G1, G4 context and G5 cleanup tests that use steps. Four G1
authored scenario companions and the selected-head companion are now present;
generated-manual qualification remains pending.

The G3 retained-history correction comes from its successor's two dirty files:
RR updates cannot omit the old manifest when that complete consumer identity
already has a retained edge. Five untracked G3 phase adapter files remain in
their source worktree: each still returns `AuthorityUnavailable`, so they were
not promoted as production implementations.

## G5 boundary provenance

The eight tracked dirty boundary paths were applied as exact patches from
`/home/yoon/dev/simple-wt-g5-successor-20260910`: runtime symbols, runtime SFFI,
interpreter extern registration/system, process facade, runtime header, owned
process implementation and its V4 selfcheck. The first two common V4 files
below came from that successor. The missing V1 schema and receipt-invariant
dependency came from the same named shared-main paths without modifying them.

| Common dependency | SHA-256 |
|---|---|
| `src/lib/common/process/observation_v1.spl` | `5a7fe32af792a30acf7f8c88aaa043bc43fef1a384e4298c5dc3e8a353f92bb0` |
| `src/lib/common/process/observation_v4.spl` | `0589ec66cc08dad7d7a98533a6b3f1b8608506e0f20ef6c29db8dc2606960d6f` |
| `src/lib/common/process/deadline_v4.spl` | `90340709f77d80c842731743a9e31a36728a146835961df5303b2b81b56d235b` |
| `src/lib/common/process/receipt_invariants_v4.spl` | `d715f5cc692ebda961ee6afa84df05a71074e639ad6c34309295b4f186c627ad` |

Two integration corrections were made to those proposals. V4 test-only failure
injection counters are thread-local, as required by the frozen concurrency
contract. The C component selfcheck now supplies a non-executable descriptor
through its existing mock pin seam to obtain a deterministic child-side exec
errno. Its prior `RLIMIT_AS=1` assumption failed: an exec attempt can terminate
after the kernel's point of no return without returning a child errno. The
replacement retains real child/pipe/error handling but is explicitly component
evidence, not production executable-pin or native Simple admission.

## Bounded checks

- Working and staged direct-env runtime guards: PASS.
- `git diff --check` / staged whitespace check: PASS.
- Executable `*_spec.spl` files under `doc/06_spec`: zero.
- V4 C component selfcheck: cycle 1 failed at the overly specific child-error
  fixture assertion; after the fixture correction, cycle 2 PASS with
  `cc -std=c11 -O0 -pthread src/runtime/test/runtime_process_observation_v4_selfcheck.c`.
  It was not rerun after PASS. Its runtime value and executable-pin functions
  are mock component boundaries, not the production ABI.
- No admitted self-hosted executable is installed in this isolated worktree.
  Compiler/lib/MCP/LSP checks, SPipe execution, generated manuals, native smoke
  and coverage remain unqualified. No Rust-seed fallback was used.

## Remaining implementation, separate from verification

1. G3 live syntax/declaration/type/trait/macro issuer ownership, confined compiler
   execution and complete affected-query scheduling are still unavailable.
   Merely importing its five closed adapters does not implement those owners.
2. G4's host inventory still lacks descriptor-bound immutable synchronization,
   selected-head replacement/directory sync, exact-operation recovery and a
   complete reader/lease/pin namespace union. The physical issuer and thirteen
   crash/restart system rows remain unimplemented; copied logical durability
   traces are not substitutes.
3. G6 still returns false from the semantic verifier/completeness availability
   gates. Portable body facts/budgets are implemented prerequisites; complete
   graph/source/generation/attempt authority and native object admission remain
   absent.
4. G5 cleanup integration fixtures still contain explicit `MissingEvidence`
   helpers for host ownership, malformed-host recovery and the complete C01-C25
   fault matrix. The passing C selfcheck covers a subset only. Production ABI,
   real pinning, deterministic race/allocation coverage and the missing recovery
   holder need implementation or independently reviewed evidence as applicable.
5. Final E/G interface reconciliation, G0 document recovery selection and
   independent integrated review remain with root. Do not fold unrelated dirty
   source worktrees into this branch or describe the candidate as verification-only.

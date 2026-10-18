# Actual block-owner HIR diagnostic — 2026-10-18

Status: HIR workaround verified; broad required checks blocked.
Tested base: release7c315aee488b679e7ad3d3d5e7afe1d6fc5b0780.
Landing base: release5c583a4967ccaf8d921804693e96babd273e9f66.

The independent object collector used runtime-stdio producer
b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab
(unchanged f04888 SPL lineage) and unmodified7c315 sources. All three actual
entry closures builtin_blocks_shell/data/math failed HIR with the same first
diagnostic: `unresolved name: block_default_examples_v1` at
src/compiler/15.blocks/blocks/definition.spl:240:9. This is the imported
BlockDefinition.examples default body, not a character-literal diagnostic.
The owners already import the other block_default_* helpers by name.

This candidate adds only the missing named helper import to each of the three
owners. It preserves default and override bodies, result shapes, and side
effects. Existing examples overrides do not prevent the current lowerer from
visiting the imported default body. The underlying compiler's declaration-owner
binding problem remains separate; this source import is a temporary workaround.
Canonical bug tags and authoritative DB reconciliation are owned separately.

Evidence: C:/dev/p4hirobject1/{shell,data,math}/compile.stderr.log and result.env.
Each compile exit1; archive and execution unproduced/unrun. The preceding real
any_audit tool generated58 cached object files after71-module HIR succeeded,
then strict linking failed on rt_cli_run_lex and other CLI runtime symbols.
This demonstrates that the collector attempted independent object generation;
it does not repair the original authority.

Regression targets are the three actual archived entry closures in
C:/dev/p4hirplan/launch-owner-object-diagnostics-cycle1.shs. A subsequent frozen,
reviewed candidate must compile each through HIR and real object generation,
record actual emitted owner symbols/capsules, and keep aggregate failure if any
target fails. The cycle2 results below supersede the original pending state.
Do not transplant independent closure objects into the203-object authority.
The live collector source, old failure snapshots, and all receipts stay unchanged.

## Cycle2 evidence and limits

Three independent genuine worktrees at4eb78b0135145016214ec5554d5b8ff9d0c1c52a
ran the real owner entry closures. HIR completed shell18/18, data18/18 and
math15/15, with zero failed HIR modules. This verifies the missing import
workaround at the failing boundary. Shell and data then failed MIR lowering
in unchanged common/json/value.spl:233:5, unsupported Result unwrap payload
type; zero objects were produced by those scopes.

Math generated five physical AMD64 COFF files with matching capsule receipts,
including compiler.blocks.builtin_blocks_math. That owner object has SHA256
recorded in C:/dev/p4hirplan/block-cycle2-coff-proof.json. The aggregate run
exceeded its8GiB guard (peak8,449,700KiB, exit88, quiescent1), so no completed
archive or executable behavior is claimed. Raw worker result.env remains
RUNNING after containment; the guard supplies its terminal status.

All evidence is retained under C:/dev/p4hirblock2/{shell,data,math}; emitted
objects remain in the canonical independent caches under p4hirobject1.
No diagnostic object was transplanted into the original authority closure.
The isolated landing patch contains only the same three import additions and
this report; JSON source changes are a separate candidate.

Required compiler/lib/MCP/LSP checks and interpreter MCP smoke remain UNRUN.
No qualified bin/release self-hosted runtime is available, and the available
b441 native producer is not a qualified complete CLI. The tracked bin/simple
fallback has Rust lineage and is not an allowed substitute. A genuine complete
self-hosted CLI is required before those gates can be satisfied; this change
does not claim production qualification or authorize bypassing failed checks.

Recovery: remove these imports only after the actual compiler binds imported
trait-default helper calls to definition-owner scope and those real closures
pass native regression. The base hash is a recovery reference, not permission
to reset another worktree. Gzip's exhausted three-admission budget is unchanged.

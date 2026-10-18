# Actual block-owner HIR diagnostic — 2026-10-18

Status: source candidate only; native repair verification pending.
Base: release7c315aee488b679e7ad3d3d5e7afe1d6fc5b0780.

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
it does not qualify the block workaround or repair the original authority.

Regression targets are the three actual archived entry closures in
C:/dev/p4hirplan/launch-owner-object-diagnostics-cycle1.shs. A subsequent frozen,
reviewed candidate must compile each through HIR and real object generation,
record actual emitted owner symbols/capsules, and keep aggregate failure if any
target fails. No second admission has been launched for this candidate.
Do not transplant independent closure objects into the203-object authority.
The live collector source, old failure snapshots, and all receipts stay unchanged.

Recovery: remove these imports only after the actual compiler binds imported
trait-default helper calls to definition-owner scope and those real closures
pass native regression. The base hash is a recovery reference, not permission
to reset another worktree. Gzip's exhausted three-admission budget is unchanged.

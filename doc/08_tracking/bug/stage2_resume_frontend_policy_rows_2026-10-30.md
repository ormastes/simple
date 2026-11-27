# Stage 2 cache resume rejects transcribed frontend policy

Status: wrapper regression passes; canonical replay and compiler admission are
separate evidence.

After the Windows executable-suffix repair, the retained
`runner-sosix-stage2-current-tools` command was refused with `transcript
environment set is not canonical`. Its five extra names were
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB`, `SIMPLE_HIR_SHARD_WORKER_KB`,
`SIMPLE_PARSE_SHARD_WORKER_KB`, `SIMPLE_PARSE_SHARD_MAX` and
`SIMPLE_SHARD_MEM_CLAMP`. The sanity memory-reserve policy was unrelated.

`bootstrap_stage3_run_transcribed` prepends these rows after the constructor
checks `bootstrap_stage3_stage2_canonical_env_names`. The resume wrapper
incorrectly compared the final transcript against the constructor-only list.
POSIX also receives the budget row (zero in monitoring mode). The focused
manifest verifier already accounts for these prepended rows.

The wrapper now recognizes this exact policy group and preserves ordered,
duplicate-free, closed environment matching. Windows values are checked
against `bootstrap_stage3_windows_frontend_environment`: a positive scheduling
share at most its default 3,000,000 KiB and the four fixed frontend controls.
This share is distinct from the enclosing RSS cap. A missing or altered member
fails. POSIX accepts a nonnegative decimal budget without the Windows share
bound; legacy transcripts without this group retain their original handling.
Windows replay exports the recorded effective share and refuses a conflicting
ambient frontend-budget override. The canonical constructor still resolves and
records the new attempt's resource controls and admission evidence.

`sh scripts/check/check-bootstrap-stage2-resume-frontend.shs` passes 26 cases:
MSVC/GNU canonical and legacy groups; Windows zero, excess, malformed, partial,
altered, duplicate, unknown and ambient-conflict negatives; POSIX legacy, zero,
positive and larger budgets with malformed/unknown negatives. The fixture
executes production validation and checks the replayed Windows share.

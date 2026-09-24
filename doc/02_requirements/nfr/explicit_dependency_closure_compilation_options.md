<!-- codex-research -->
# Explicit Dependency-Closure Compilation — Selected NFR Option

## Selection

**Selected:** balanced production performance with correctness-first count gates.

The user authorized a 10% target or a better assigned value. The selected gate
requires clean warm builds at ≤25% and private/comment edits at ≤35% of the
current entry-closure baseline, while retaining ≤10% maximum regression for the
bootstrap/source-led migration path.

Mandatory gates include zero live-worktree reads after freeze, zero hidden
recursive discovery, zero Git/SCV user-state writes, exact dirty-package source
open bounds, deterministic outputs, crash-safe publication, ≤110% max RSS, and
quiet receipt-backed operation. Unselected NFR alternatives were removed.

**Pros.** Demands a visible Java/Go-style speedup without making the first
rollout depend on aggressive section encoding; count gates catch hidden work even
when wall-clock noise is high.

**Cons.** Requires realistic fixtures and admitted baselines; later releases may
still ratchet metadata p95 from 64 KiB toward 16 KiB.

**Effort.** M beyond implementation: benchmark fixtures, access tracing, crash
matrix, Git-state immutability checker, and daemon RSS evidence.

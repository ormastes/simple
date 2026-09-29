# Bootstrap cache preservation and explicit invalidation

Compatible bootstrap caches are reused by default on Linux, macOS and Windows.
The Windows batch entrypoint forwards the same flags to the canonical engine.
Compiler rebuilds, one-binary mode, successful Phase 2 completion and cache age
never authorize deletion. Failed attempts retain completed native objects,
frontend records, runtime objects and logs.

## Commands

| Command | Scope |
|---|---|
| `--invalidate-cache=stage2` | The selected Phase 2 compiler entry cache |
| `--invalidate-cache=stage3` | The selected Phase 3 compiler entry cache; valid with Phase 3 resume |
| `--invalidate-cache=stage4` | The selected full CLI entry cache |
| `--invalidate-cache=stage4b-ui-backend` | The selected UI backend entry cache |
| `--invalidate-cache=stage5N` | The selected MCP entry cache |
| `--clean-rebuild` | Each build entry cache requested by this invocation |
| `--fresh-cache`, `--no-cache` | Compatibility aliases for explicit clean rebuild |

After a source or compiler fix, explicitly invalidate its affected phase. A
changed binding refuses default reuse with an actionable diagnostic and keeps
the old files. It never rewrites a producer identity or stamp to admit old
objects. The phase binding records schema, phase, exact producer SHA-256, entry,
and a digest of source identity/content, backend/mode, runtime and resolved tool
snapshots, ABI/plugin/K1/coverage/link options. Stage 3 additionally binds its
actual assurance profile and warning policy. Later tool entries use the
compiler's canonical semantic environment field list, after their actual
forced overrides, including CPU, linker, MIR bulk operations and safety profile.
The full CLI records its actual one-binary mode. Phase 3 additionally binds the
bytes of the genuine, fully verified Stage 2 ABI admission receipt. Resume
forwards that receipt and its matching recorded policy through the hermetic
worker, and refuses an absent, changed or different-producer transfer. Cache
configuration and forwarding checks do not replace compiler admission.

Phase 2 and Phase 3 retain the canonical cache roots committed by their
transcripts and use separate immutable producer/entry bindings. Later tool
entries use `native_cache/<phase>/<producer-sha>/<entry>`. Inner cache owners
still validate object contents, dependency keys and runtime/tool ABI. Explicit
phase invalidation clears its entry's native/frontend/runtime cache contents;
other phase and entry caches remain. No per-module retention guarantee is made
for a changed phase binding.

## Manual clean

Run from Git Bash/MSYS2 on Windows or the native Unix shell, using canonical
absolute paths:

```sh
sh scripts/bootstrap/clean-bootstrap-cache.shs \
  --root /absolute/owned/cache-root --lineage /absolute/owned/cache-root/selected-entry
```

The command checks root ownership, exact metadata schema, path containment and
links, and acquires the lineage's exclusive writer lock. Active, unknown,
corrupt or unbound caches are refused. Admission receipts, source trees,
compiler binaries and attempt evidence are outside the clean scope.

A normal failed build releases its writer after the build stops, so a matching
retry resumes completed work. A signal or forced process termination retains
the writer when shutdown is uncertain. A dead wrapper PID alone cannot prove
its descendants stopped. The current lock records identify only the acquiring
wrapper; execution can continue in another session, cgroup or systemd unit.
`--repair-idle-writer=RECORDED_NONCE` checks ownership and identity, then refuses
these incomplete records without removing the lock or cached objects. Neither
a nonce nor an absent wrapper process group proves execution stopped.

Genuine execution-owner registration and unit/group verification for manual
crash repair remain an open follow-up. There is no automatic crash-lock
reclamation or supported manual removal of an unresolved writer. Caught-failure
retry and explicit clean of an owned idle lineage remain available.
## Evidence and progress

Each retry gets a unique attempt archive. Terminal files have SHA-256 receipts
and read-only permissions; prior results are retained. Cache contents remain
mutable within their single writer lineage. Cache progress is concise and based
on actual compiler counters, for example `Cache: reused 117 modules; rebuilt 2.`
Enabling a cache or finding a directory is never reported as a cache hit.

Focused contract: `test/01_unit/scripts/bootstrap_cache_lineage_resume_test.shs`.
It exercises partial failure/retry, incompatible bindings, explicit invalidation,
idle/active clean, signals, forced termination, manual repair refusal and receipt
counters without a full bootstrap.

The original focused owner contract passed once on Windows Git Bash and once on Linux
Ubuntu WSL using private fixtures. These checks verify admission, preservation
and cleanup rules; they do not verify a full compiler build. The native compiler
summary change remains subject to the next candidate's normal compiler smoke.

## Repair loop

Use caches aggressively while failures are being fixed. Before starting a new
attempt, find the previous cache for the same phase, producer and entry and
inspect its binding and failure log. A new attempt or worktree is not a reason
to choose an empty cache. Keep the immutable source identity needed by the
matching lineage; changing that identity requires selecting or explicitly
invalidating a justified scope. Preserve Cargo authority targets and completed
native/frontend/runtime work on failure. Ephemeral HOME/config/tmp cleanup is
separate from build cache invalidation.

Managed bootstrap entries explicitly set `SIMPLE_FRONTEND_CACHE=1` and
`SIMPLE_HIR_CACHE=1`, with directories under the admitted entry's `frontend`
and `hir` children. Their actual settings are bound into the cache inputs.
The compiler still enforces its feature and semantic-policy admission rules;
these settings do not authorize incompatible cache hits. Existing bindings
from before the explicit HIR settings require justified scope invalidation.

Keep frontend and HIR persistence enabled throughout repairs. Inherited
`SIMPLE_FRONTEND_CACHE=0` disables both; a cold-cache timing or RSS comparison
alone does not justify disabling them. A bounded diagnostic may disable
persistence only for a concrete correctness blocker, and must restore it for
the next repair attempt.

Invalidate changed dependencies only when the cache owner's dependency/content
validation can prove unaffected entries remain valid. The current wrapper's
explicit invalidation is at phase entry scope, so it conservatively clears that
entry on a binding change and retains unrelated phases and entries. A producer,
runtime/tool ABI or schema mismatch cannot use old objects. Report the mismatch
reason and available cache path; never label cache configuration as a hit.

Run a final explicit clean rebuild only after the build failures are fixed and
focused verification passes. That clean rebuild is deferred during the repair
loop. This update's focused validation is separate from the ongoing native
Windows/Linux bootstraps; no running cache is cleaned by the contract fixtures.

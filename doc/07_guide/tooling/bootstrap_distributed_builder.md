# Cached bootstrap with a distributed builder

Implementation and qualification are in progress. This guide is the intended
workflow, not evidence that the manager or either host has passed.

The user's September 30 priority is grouped isolated local builds, with
distributed execution later. Follow the
[main-audited grouping plan](../../03_plan/compiler/bootstrap/grouped_isolated_build_manager_2026-09-30.md).
Build this bootstrap manager with the genuine Phase 1 seed and retain the
qualified executable through Phase 4. This tool-production exception does not
authorize substituting the seed for later phase compilers or test runners.
Reuse main's SCC scheduler, action coordinator and artifact service.

Continue eligible canonical bootstrap scripts while building the manager in a
separate source lane. Preserve input paths and compatible caches. A new manager
must not hold up an independent cached build. Follow the script's real admission
guards; diagnostic progress does not supersede formal phase qualification.

Build the manager with the Phase 1 seed, retaining a cache bound
to phase, producer digest and manager entry closure. The seed is permitted for
bootstrap production of the self-hosted compiler and this manager. Before adoption,
require manager qualification and the actual scheduled phase's prerequisites, including
local execution, worker failure, restart, keep-going/fail-fast, cache reuse and
invalidation. A manifest syntax check is not a lifecycle test.

Stage 2 seed execution needs actual outer manager supervision if the seed lacks
the new internal manager hook; forwarded but ignored environment variables are
not adoption. Existing native jobs finish under their original owner. Adopt at
the next idle, legitimately admitted boundary without changing live inputs.

Only set manager integration options after qualification. The compiler and
canonical bootstrap transfer must agree on the manager executable digest, host
manifest, LLVM tool identity, and source/producer inputs. A configured but
unqualified or unsupported route must fail explicitly. An unset manager leaves
the existing script route available.

The manager owns dependency admission, journal and publication. Each worker
owns its process tree and isolated writable files. Immutable LLVM IR files can
cross the code-generation boundary; live MIR objects and backend sessions cannot.
Frontend module/SCC isolation remains a distinct requirement. Whole-binary
scheduling, local execution or protocol simulation alone does not demonstrate
distributed module compilation.

Use only explicitly configured hosts. Record local versus actual remote tests
separately. Preserve failed attempts and valid completed outputs. Retry only
after owned cleanup/reaping is established; a polling timeout or missing
heartbeat alone does not establish process death. Manager restart must recover
ownership through identity-bound worker control, never an unverified reused PID.

Record measured cache hits/misses/stores. Unknown telemetry must remain unknown;
the existence or count of cache files is not reuse evidence. Separate compiler
cache metrics from manager-level reuse of completed task outputs.

See [active ownership](../../03_plan/agent_tasks/bootstrap_parallel_resume_2026_09_30.md)
and [execution report](../../09_report/bootstrap_parallel_resume_2026_09_30.md).

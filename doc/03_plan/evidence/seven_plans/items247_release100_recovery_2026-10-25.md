# Recovery and port to release/1.0.0

STATUS: UNVERIFIED. No Phase3 PASS or merged PR.

The requested target is release/1.0.0, frozen at
14de106c80d5498ed6f7c9df2620a45b5f51d5c4. Main checkout release/1.0 was
clean and remains untouched. The new owned branch/worktree is
work/items247-release100-20261025 at
/home/yoon/dev/simple-items247-release100-20261025.

The prior worktree's Git registration and private commit objects disappeared
from the main repository metadata. Its files, build logs and evidence remain.
Cycle7's prior bootstrap stopped at sanity when Git lookup failed; no Phase3
was admitted. Both owned kernel scopes are inactive. This is infrastructure
failure evidence, not a passing compiler test or a new compiler cause.

A separate temporary Git index recovered the preserved old worktree's delta
against known base5120e296997. The source files were not changed. The recovery
patch contains56 owned paths and excludes vendored runtime source. Its SHA256:
795697909f3a62330468ab94a35034daaa7e171c09ea19c136a1a5624d5ae8ac.
The patch and per-path statistics remain in the predecessor worktree under
build/native_probe/recovery-release100-20261025/.

Three-way application produced two conflicts. HIR expression_components keeps
upstream pattern_enum_substitution imports plus our integer-pattern normalizer;
it does not resurrect the old in-file substitution helpers. Constructor
lowering keeps upstream array-initializer and move-ownership helpers plus the
exact-provider constructor layout and fail-closed metadata check.

A smaller-model read-only audit was guided and independently reviewed by root.
The new release's call-returned array/slice owner recovery and erased-record
boxing changes complement, but do not replace, qualified parameter layout,
complete copied HIR provenance, exact custom operator dispatch/inequality, or
qualified construction. No audit establishes native behavior.

Recovered source includes checkpoint actual-byte accounting; gzip filename
narrowing; suffixed integer-pattern normalization; imported-record operator,
constructor and parameter-copy fixes; and associated real native/MIR fixtures.
Historical failure receipts retain their original source/producer identities.
The exit22 last-field comparison remains the unchanged decisive native oracle.

Remaining: execute the decisive native regression with a source-matched compiler,
build Phase3 and run Hello with that exact compiler, complete core/lib/MCP/LSP
and SPipe/manual qualification, then review and merge the owned PR against
release/1.0.0. Broad retained item2/4/7 gaps require fresh target-specific evidence;
older production-boundary reports are historical and are not silently treated
as current completeness claims. All prior cycle counts are retained; recovery,
new branch and target do not reset the budget. No direct protected push is used.

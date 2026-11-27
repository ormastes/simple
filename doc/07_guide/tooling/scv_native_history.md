# Native SCV history

`scv log --all-parents [bookmark]` reads the current workspace or the named
bookmark and prints every reachable loose commit once. The order is depth
first in stored parent order: a diamond with parents left and right prints
merge, left, shared base, right. This is deterministic traversal order, not a
topological ordering. Existing `scv log` and `scv log <bookmark>` retain their
existing behavior and output.

`scv change-log [change_id]` prints the selected logical change's open/closed
state and the revisions reachable from its recorded `latest`, filtered by
that stable ChangeId. Without an ID it selects the current commit's change.
An explicitly selected change can be inspected even when its latest revision
is outside the current workspace ancestry. Legacy change records without a
state field read as open.

The output is reachable ancestry of latest. It does not reconstruct abandoned
versions or earlier non-ancestor rewrites. The mutable change record currently
stores only one predecessor, so it cannot supply an immutable evolution log.
Closing a change and starting a new one remain the existing `close-change`
and `new-change` operations; these commands do not change their publication
or crash behavior. `restore-op` retains its existing safety limitations.

History uses native SCV files and does not invoke Git or jj. The first version
requires readable loose objects; packed-only objects return an explicit
error. Missing, nonregular, unreadable, malformed, and cyclic objects fail the
whole request with a nonzero CLI exit and no partial commit rows. A missing
bookmark is an error; an unborn workspace prints `no commits`.

Each metadata/object read is bounded to 1 MiB through the checked regular
file reader. Graph traversal admits at most 10,000 commits, 50,000 parent edges
(including duplicates), and 16 MiB of cumulative commit text. A newly loaded
object can occupy up to the per-object bound before the cumulative admission
check rejects it. Pending traversal frames are bounded by admitted nodes and
edges. Workspace/change metadata has separate per-file bounds. Validation
covers reference shape and required fields; `fsck` owns content-hash and tree
integrity checks. These reads do not establish repository-wide snapshot
isolation against concurrent writers.

Run the executable specs with an admitted pure-Simple runtime and an absolute
`SIMPLE_SCV_TEST_RUNTIME` path. Runtime execution and manual generation for
this addition are currently **NOT_RUN**, pending that runtime.

- Integration: `test/integration/app/scv_native_history_spec.spl`
- CLI scenarios: `test/03_system/app/scv/feature/scv_native_history_spec.spl`
- Implementation: `src/lib/scv/history.spl`

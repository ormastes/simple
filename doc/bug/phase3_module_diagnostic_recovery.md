# Phase 3 collection after a failed aggregate build

The provisional Phase 3 scheduler previously marked its entire module group
BLOCKED when the full index failed. This did not establish whether individual
modules could lower and emit objects.

When the Phase 3 index or group fails, the scheduler now attempts each module
inventory entry using a separate generic build-manager task with `--emit-object`.
Each task retains the existing producer selection, pinned source checks, image
verification, resource policy, private persistent cache and terminal receipts.
The configured thread count is retained. Backends keep separate journals and
caches. No partial index is accepted as valid input.

Ordinary failures and process exits (including crash exit codes) do not stop
later independent entries. Each diagnostic row records the entry, exit code and
outcome. Successful object emission is `OBJECT_EMITTED_UNQUALIFIED`; it does not
replace the failed index/group status or satisfy final phase admission. An
authority failure still prevents that task from invoking the compiler. Invalid
inventory paths stop the affected lane before diagnostic task construction.

These tasks exercise each entry's valid compilation path through object output;
they cannot execute MIR or linking with nonexistent/invalid prerequisite IR.
Link qualification remains separate. Completed group builds do not trigger this
fallback. Live attempts keep their immutable scripts; apply this change to the
next admitted runner invocation.

Validation: the new shell scheduling control covers index failure, group failure,
ordinary failure, crash exit 139, blocked exit 20, later successful object output,
both backends and subsequent Phase 4 scheduling. It passed. The existing
provisional scheduling control also passed. These are host orchestration tests,
not real compiler/native bootstrap evidence. Native verification remains pending.

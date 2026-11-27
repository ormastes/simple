# Darwin BuildRunner rejects every staged producer at chmod

Status: fixed; native macOS command evidence and production manager interpreter
regression. Baseline: `fbb3fcb4a24` (partial recovery cleanup).

The local transport invoked `chmod` with `["500", "--", producer_path]`.
Darwin's chmod stops option parsing at the mode operand, treating the following
`--` as another filename. On native macOS arm64, `/bin/chmod 500 -- <file>`
returned 1 and `chmod: --: No such file or directory`, even while changing the
actual file to mode 0500. BuildRunner then rejected the launch as `cannot make
staged producer executable`; the worker spawn operation was never reached.
The SSH command used the same invalid operand order.

Both command forms now place the option terminator before the mode:
`chmod -- 500 <path>`. The native corrected command returned 0 and mode 0500.
No argument is removed, shell quoting is unchanged, and the producer remains
readable/executable only by its owner. Windows skips this unchanged branch.

## Executed regression

The existing `failure_dispatch_spec.spl` invokes the production manager and
transport with a counting worker process port. The real local staging chmod
runs on macOS; the compiler/worker spawn remains a test operation, so this is
not native compiler execution or containment evidence.

The old fixture was stale. It now imports the existing locked loop from its
canonical BuildRunner owner, passes the explicit absent database, declares a
distinct output per task, expects a restored uncertain attempt to reserve a
RUNNING slot, and requires a cached terminal wait to avoid reusing a consumed
process token. These repairs restore the intended dispatch-policy checks.

Using the retained Phase 1 producer generation
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
from `/Users/ormastes/wt/release-bootstrap-integration-20261025/src/compiler_rust/target/bootstrap.generations/`, run:

```
SIMPLE_LIB=src <producer>/simple test test/01_unit/app/bootstrap_builder/failure_dispatch_spec.spl --mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon --sequential
```

- Initial diagnostic: all four intended launch scenarios failed before spawn
  at chmod. Log `/tmp/buildrunner-partial-recovery-red.log`; that run also
  contained a separately failing recovery-cleanup case since moved to its
  own spec and fixed in PR #5208.
- After correcting chmod, 4/5 passed; the remaining assertion incorrectly
  expected a second wait on a consumed token. The actual owner reuses its
  cached completed observation. Log `/tmp/buildrunner-chmod-green.log`.
- With the stale assertion repaired, **5 total, 5 passed, 0 failed**.
  Log `/tmp/buildrunner-chmod-final-green.log`. This covers exact ERROR replay,
  uncertain observation, malformed collection, two owned workers, retained
  journal reservations and bounded cancellation requests.
- Working environment guard and whitespace checks passed.

Native SSH execution and GNU/Linux execution were not run. Full native
BuildRunner Hello remains blocked on Darwin V4 containment/worker ownership;
no admission guards were changed and no Phase 2 rebuild was performed. This
fix removes an earlier deterministic macOS launch rejection, not the remaining
V4 capability blocker. Full compiler/lib/MCP runtime gates remain unverified.

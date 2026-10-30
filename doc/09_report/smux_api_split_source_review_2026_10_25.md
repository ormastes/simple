# Smux API split source review

Baseline: `fbc97292aa1daaf07c47b083f718869b44213cba`.
Worktree: `D:/dev/simple-smux-integrated-20261025`.
Frozen source reviewed at integrated HEAD `2ebef3106aa`; that evidence commit
does not alter the source baseline. **Status: WARN / source review complete.**
No concrete P0/P1/P2 regression was identified in the three-file extraction.
Compilation and native execution: **NOT_RUN**. No compiler, test, docgen or
product process was launched. This is not production verification PASS.

## Independent source findings

- Independent declaration comparison found the public API signatures identical
  to the baseline. The API retains `_svc`, leases, closing sets, checkpoints and
  authoritative commit ownership. The new helpers take explicit state and
  return concrete typed update records; they have no API/global-state imports
  or callbacks.
- Wrapper commit flags preserve zero-write refusals/read-only queries and the
  existing single-write paths. Successful polling still commits even without
  a state difference, preserving its original write frequency. Send-command now
  delegates within the explicit-state owner and returns its update to one API
  commit; it does not invoke a second public API writer.
- Failure-side effects were compared explicitly: failed send flush retains its
  input error; a failed PTY pending query commits the error record; paste queue
  refusal retains the prior drain/reply state. Paste still drains without
  flushing, appends its payload, and makes one write attempt. Failed frame
  construction after drain still commits the changed state and capture metric.
  Early invalid history/target checks remain before native effects and commits.
- Closing-state checks use supplied booleans or bounded closing-ID snapshots.
  Native read budgets, write limits, terminal query ordering, capture metrics
  and error text remain aligned with the original bodies. Read-only native
  liveness and explicit checked PTY close retain their original closing-state
  behavior; this extraction does not add a new lifecycle policy.
- Split still validates before native resize, allocates the same pane ID,
  updates geometry, captures/filters checkpoints, then performs one service
  commit. Resize/arrange return complete state only after the existing native
  effects and best-effort resize rollback. Helper extraction does not claim
  native rollback is atomic beyond the baseline contract.
- Import direction is acyclic in the affected graph: API to pane I/O and window
  layout; pane I/O to frame snapshot; frame snapshot and checkpoint to window
  layout. Window layout does not import checkpoint or API. Primitive service,
  geometry and VT dependencies do not introduce a reverse API edge.

The author's frozen total-line receipts are API751 (limit780), pane I/O461 and
window layout271 (each limit600). These already-passing counts were not rerun.
The inspected decomposition follows pane-I/O and window-layout responsibilities,
and the function mapping/design matches the frozen code.

## Scope and remaining qualification

Only the frozen three source files and their mapping evidence were reviewed.
Materializer alias dirt and other integrated work were preserved and excluded.
Reset, best-effort pane release and failed-spawn cleanup retain their original
semantics; this mechanical change does not qualify or repair those paths.

The existing input-queue, capture/history/frame, geometry/rollback and lifecycle
regressions remain required on an admitted producer. Static comparison cannot
prove the compiler's concrete record-return ABI, native provider effects or
error-side state visibility. There are zero newly executed acceptance cases.

## Exact frozen SHA256

| File | SHA256 |
|---|---|
| src/os/apps/smux/api.spl | 61b9d03bbc34971aba0f2f8c0ef83b81ca184b3602a8bc03dddce7ce961a385e |
| src/os/apps/smux/pane_io_service.spl | 0305140f7d17d31ab4d33a65e2bac7e8d626630e197283f3b83314c039df8021 |
| src/os/apps/smux/window_layout_service.spl | 90946e15c175ec08547159409aaff20f05f8e2c0a370fe28303f7f6e03ecc714 |

Supporting mapping: `doc/05_design/smux_api_owner_extraction_2026-10-25.md`.
Author source receipts: `doc/09_report/smux_api_owner_extraction_2026-10-25.sdn`.

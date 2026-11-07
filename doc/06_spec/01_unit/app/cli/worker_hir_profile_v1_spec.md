# HIR worker profile policy

Status: NOT_RUN. This manual describes authored unit assertions, not execution.

The spec exercises the production argument validator with an accepted explicit
closure and rejects absent closure, mixed MIR/parse/file-unit modes, plugin and
unknown routes, incomplete option values, invalid shard ordinals and duplicate
shard selections. The environment policy accepts canonical source authority and
rejects loader injection and unadmitted routing keys.

Retirement-deadline controls exercise the helper used by the owner: the first
terminal/error observation sets one5000ms deadline, repeated acknowledgement
attempts cannot extend it, and unavailable/overflowing clocks do not establish
an elapsed-time budget. These controls are not native acknowledgement/clock
fault injection. The paired integration spec uses an actual retained process
lease for cancellation, rejected-ticket and controlled clock-observation cases.

No native-provider, branch-coverage, latency or generic-tool guarantee is implied.

Additional controls verify prelaunch remaining-budget rejection when the clock
is unavailable and canonical sorting without changing the captured environment
values or input order. These are production helper tests, not provider evidence.

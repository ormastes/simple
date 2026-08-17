# Bootstrap diagnostic sweep could not resume terminal rows

- Date: 2026-08-16
- Owner: `/root/sweep_planner`
- Status: fixed, focused verification pending
- Scope: diagnostic inventory runner only; this is not Stage 3 or Stage 4 acceptance evidence

## Problem

The durable bootstrap diagnostic sweep created an inventory but had no exact
resume operation. A restart therefore risked rerunning already-terminal checks,
including green rows, or mixing results from changed inputs and executables.

## Contract

`--resume` must byte-validate the frozen manifest and run identity and validate
the recorded compiler and delegated-child content hashes. Only a one-line,
schema-valid, atomically published terminal result is reusable. Every valid
terminal class (`pass`, `failure`, `signal`, `timeout`, and `infrastructure`) is
skipped. Missing, corrupt, or partial rows are quarantined and redispatched.
Ordered aggregate results and the summary are rebuilt atomically from the
manifest. Ordinary mode rejects a nonempty evidence directory.

## Verification

One combined shell syntax check and one fake-runner integration fixture are the
only authorized checks. The fixture covers frozen-identity rejection, terminal
failure/signal/timeout preservation, missing-row redispatch, corrupt-row
quarantine, and ordered complete summary reconstruction. No Simple compiler,
bootstrap, or real Stage 4 sweep is launched by this verification.

## Observer-v2 follow-up

The retained cycle-3 discriminator proved that the watchdog could kill the
Perl wait-status observer together with its child process group.  That erased
the typed child outcome and forced an intrinsic signal into the legacy timeout
path.  Observer v2 keeps the sole outcome publisher outside the killable child
process group.  The observer and watchdog atomically claim terminal-versus-
deadline ownership; the watchdog separately receipts its TERM/KILL request.
Only a deadline-first outcome with a validated watchdog action can be timeout.
An unexpected signal remains a signal, and a missing or malformed outcome is
infrastructure failure.  The run identity binds the v2 classification policy
and exact runner hash so old receipts cannot cross this semantic boundary.

The focused discriminator is one host-C row with core dumps disabled that
raises `SIGSEGV`.  It must terminalize as status 139, signal 11, with no
deadline receipt, and an exact resume must dispatch neither the row nor a
preflight.  The existing mixed fixture remains the timeout and corrupt/missing
resume control.  No execution is authorized until final-review approval of the
frozen diff and hashes.

Every reusable terminal row also owns an atomic evidence-hash receipt binding
its result and log plus its command, deadline, and watchdog receipts when
present.  A result whose shape is valid but whose bytes no longer match that
receipt is nonterminal for resume purposes, is quarantined, and is redispatched.
Result and log hashes are mandatory for every class, including infrastructure,
and logs must be regular non-symlink files; only internal command/deadline/
watchdog artifacts may be absent where the terminal class permits it.
Quarantine slot allocation checks every known suffix (including partial status,
claim, log, and evidence receipts), so an older incomplete slot is never
overwritten.

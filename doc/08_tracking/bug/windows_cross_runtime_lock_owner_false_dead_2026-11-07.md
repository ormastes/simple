# Windows cross-runtime lock owner falsely reported dead

Status: repaired candidate independently approved; Windows host checks have
passing evidence across bounded runs. Linux qualification is blocked.
This is a host lock prerequisite repair, not compiler or bootstrap admission.

## Original failure and scope

Release base: `4ff1e3b51f54042b919e5a1280f556cda6e79d4a`.
Implementation worktree: `D:/dev/simple-lock-cross-runtime-20261107`.

Independent original evidence remains in
`D:/dev/simple-node-attribute-bootstrap-20261106/build/node-attributes-qualification/attempt12-terminal/`:
`cross-msys-live-claim.sdn`, `REPORT.md`, and retained claim/lock observations.
MSYS2 Perl reported `dead` for Git Bash POSIX owner 31446/group 31446 while
its encoded native identity `windows:20284:134384928162024064` still matched
the live native process. The compared helpers had identical SHA256
`fc08ed1a45920e0deb4d2cbac1ad950cfecb5f127f8bc6982ac263273ee2c0e9`.
No original claim, owner, cache, or attempt12 artifact was changed here.

The owner helper required a local `/proc/<pid>/winpid` mapping. Independent
Git Bash/MSYS2 runtimes have different POSIX PID namespaces; missing local
PID/group entries cannot establish absence of that foreign owner or children.
The orphan reaper similarly treated unauthenticated numeric POSIX group IDs
as signal targets after a `live` claim verdict.

## Contract and repair

The claim's decoded native Windows PID and creation FILETIME are consulted
before local PID/group checks. A matching native observation means `live`.
Missing/reused/unreadable native owners, malformed native tokens, observer
errors/timeouts, and a non-Windows observer mean `unknown`: foreign children
cannot be excluded. Hex must contain complete lowercase bytes; odd-length
hex is rejected with exit 2. Linux/legacy non-native identity logic is retained.

The existing native observer invocation/output/timeout validation is shared
with the normal owner snapshot path. Snapshots still verify their local
PID/native-PID/group mapping on both sides of native observation.

The shell orphan reaper now receives the expected start token and refuses
native `windows` tokens before any local PID/group probe or signal. This
deliberately prevents automatic recovery of native-token claims whose owner
is gone: the manifest does not authenticate a foreign group's absence.

## Private regression evidence

`scripts/check/check-portable-lock-cross-runtime.ps1` starts and releases its
own private Git Bash lock owner, queries it from MSYS2, attempts private lock
contention, checks unchanged claim bytes/hardlink identity/native generation,
and records every verdict. Group-collision reaping uses a recording `kill`
function; no real signal is sent. Wrong birth simulates a reused token, not
actual OS PID reuse. Private shadow observers exercise nonzero exit, malformed
output, and timeout. `-CheckGroup observer` reruns only observer-failure checks.

The original helper/library produced eight failing private checks, including
cross-runtime `dead` for a live owner and attempted mocked group signals.
The candidate's expanded run passed 20 of 23 checks; three observer-result
checks failed because the fixture incorrectly put a Windows drive path into
POSIX PATH. The fixture now converts that path with `cygpath`; the focused
observer rerun passed all six observer assertions. The 23 distinct checks
therefore have passing evidence across runs; no final all-group rerun or
full bootstrap/test-suite PASS is claimed.

Evidence handling error: a later sparse-checkout expansion removed ignored
private `before`, `after`, `after2`, and baseline fixture directories. Their
terminal results survive only in the session transcript and are labeled as
such in the retained report; those logs have not been reconstructed as raw
execution artifacts. Original attempt12 evidence is independently retained
and untouched. The focused run remains at
`build/lock-owner-regression/observer-after4/`.

The existing `scripts/bootstrap/tests/portable-lock-stale-owner-test.shs`
now has a Windows control for a private short-lived owner with no child
descendants: its exited native claim must remain `unknown`, contention must
return 75, and no recovery may occur. The live-owner control and POSIX orphan
recovery branch remain. The Windows invocation passed both cases; its raw log
is retained at
`D:/dev/simple-lock-cross-runtime-evidence-20261107/windows-stale-owner-test.log`.
The focused observer run was also copied into that external evidence archive,
alongside `REPORT.md`, `verification.sdn`, and explicitly labeled terminal
excerpts, so subsequent sparse-checkout operations cannot remove those records.

Perl syntax and tracked source whitespace checks passed. Attempted Linux
stale-owner regression could not start: Ubuntu-24.04's configured ext4 VHDX
is missing (`Wsl/Service/CreateInstance/MountDisk/ERROR_PATH_NOT_FOUND`).
Docker's Linux engine pipe is also absent. Existing Linux live/dead/reused
group behavior and the non-Windows native-token branch require Linux runtime
qualification; they have only source review here.

Independent reviewer `/root/astra_linker_final` approved the five-path repair
with no blocking/P0/P1 source findings and read the retained Windows selftest
PASS log. Reviewed helper SHA256:
`0bdff03896adf62d86ebfd348bf08b5239c58e394ff9efee0ca2e4c325961ca8`;
shell library:
`472f1397f96553c50a8cb033a480980d3485ee1b557c899e3cc119bfc89f7b8f`;
cross-runtime harness:
`e390c99decb9e4eba5321796924b05983d6ac40057994cd1137ab88d983011e1`;
stale-owner regression:
`4e610b22cebda6980e9806a3a9b8f9b3601fb6798a721a6de83dd384c5719f08`.

## Mixed-version coexistence

Only patched observers enforce this contract. An active old peer can still
misclassify or reap a foreign-runtime claim. Do not claim global mixed-version
safety or modify another lane to retrofit this fix. Bootstrap continuation
must wait for existing owners to finish or use a coordinated compatible
runtime/updated-helper arrangement under normal locks. Preserved frozen
builds and shared caches must not be changed in place.

# Native session runtime digest must select the capsule archive layout

The standalone runner built with admitted producer `5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`
from the 80-path consumer manifest `da6c7966a4c578d0a4c710eb67728d21e7bfed161a98a7167864e865be77be58`
acknowledged and cleanly retired its private daemon, but rejected plain-green
before the test body: `invalid native session digest: runtime_sha256`.
Receipts: `D:/dev/simple-runner-env-consumer-evidence-20261030/accept-plain-green-1793358994310326200`.
This is independent of the earlier environment snapshot payload repair.

Both request minting and daemon binding revalidation appended
`/libsimple_native_all.a`. The selected MSVC producer capsule instead contains
`simple_native_all.lib`; hashing a nonexistent `.a` returned an empty digest.
The bootstrap capsule authority in `scripts/bootstrap/phase2-runtime-binding.shs`
already accepts the MSVC `.lib` layout and GNU/POSIX `.a` layout, rejecting both
being present. Linux, macOS and BSD retain their `.a` behavior.

The shared runtime authority now resolves the sole regular native-all archive
inside the already selected absolute capsule root. Missing, ambiguous and
nonregular leaves refuse admission. Both native session digest sites use that
resolver; doctest sessions inherit the same request/binding path. No archive
alias is created. Worker, producer, environment, runtime snapshot, tool authority
and digest checks remain required. The resolver does not select another runtime
provider or replace the managed snapshot admission.

`test/fixtures/compiler/native_runtime_capsule_archive.spl` exercises real files
with distinct `.lib` and `.a` bytes/hashes, missing/both rejection, relative-root
rejection and a directory posing as an archive. Supply an absolute absent
`SIMPLE_RUNTIME_ARCHIVE_FIXTURE_ROOT` in an isolated evidence directory.
Independent Astra source review cleared the four-file repair before integration.

Focused native execution passed on attempt 03: build exit 0, run exit 0,
`NATIVE_RUNTIME_CAPSULE_ARCHIVE_PASS`, 73 compiled modules. The executable SHA256
is `bc9da409e3705d9b35802650d32f71977394b97ddafa6e305f1b93ee0dd9bfa6`.
Producer remained the admitted `5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`;
the frozen 86-path consumer manifest is
`3b9c2554f4593c3020be46afaef3b2e621cd6fc9d2bdf36cd52788d8bacf5fd4`.
Receipts: `D:/dev/simple-runner-archive-consumer-evidence-20261030/regression-runtime-archive-03`;
policy: sibling `archive-attempt03-policy.sdn`.

Attempts 01 and 02 refused memory preflight (exit 3); neither began native
compilation. Their receipts remain preserved. Attempt 03 used an explicitly
authorized, independently reviewed 1 GiB host reserve for this small fixture,
an enforced 8 GiB RSS cap, one requested thread, low-memory mode and the
unchanged normal admission guard/worker clamp. Build peak RSS was 4,895,012 KiB;
run peak RSS was 2,560 KiB. Both process trees were quiescent at completion.
The full runner retains its normal 4 GiB reserve; this fixture policy does not
authorize a broader reserve reduction.

This PASS qualifies the archive-selection fixture only. Daemon SSpec test-body
acceptance and required broad checks remain pending; no SSpec PASS is claimed.

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
Source review and native execution are pending; no SSpec or daemon test-body
PASS is claimed by this repair.

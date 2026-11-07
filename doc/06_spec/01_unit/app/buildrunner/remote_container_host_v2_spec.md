# Remote container projected action binding V2

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, tests, provider, filesystem fixture, or container was executed.
No runtime PASS or execution provenance is claimed.

Source: `test/01_unit/app/buildrunner/remote_container_host_v2_spec.spl`.
Owner under test: `src/app/buildrunner/remote_container_host_v2.spl`,
`remote_container_action_bind_v2`.

These specs construct actual common `ContainerActionProjectionV2` and
`ContainerMountProjectionV2` values around an existing task value fixture. They
exercise only action projection binding. The helper requires exactly one
writable mount with the exact admitted host root, `producer.exe` and `work`
beneath its guest root, and every original task argument in order. Guest root,
executable, and working-directory backslashes normalize to forward slashes;
host-root and argument bytes retain exact comparison.

| Scenario | Intended assertion |
| --- | --- |
| Exact Linux action | One writable mount, exact executable, original argv, and guest work directory accept. |
| Exact Windows action | Windows guest slashes normalize consistently, including mixed guest-root spelling; original argument bytes and spaces remain intact. |
| Wrong program | Different or empty executable rejects on both platform path styles. |
| Different arguments | Substituted and reordered arguments reject on both platform path styles. |
| Argv shape | Empty argv, a missing argument, and an extra argument reject without indexing absent entries. |
| Wrong host root | Otherwise matching Linux or Windows action rejects for another admitted host root. |
| Wrong guest cwd | A different attempt's work directory and a guest-root-only cwd reject. |
| Mount shape | Missing, read-only, and additional mounts reject on both platform path styles. |

The host source routes lifecycle operations through the Simple Container API,
retains original wait/log observations, requires independent exact native-object
absence after destruction, captures bounded output bytes, refreshes protected
authority before signing, and emits a distinct container V2 completion. These
pure action specs do not qualify those lifecycle, capture, cleanup, authority
refresh, timing, or signing behaviors. Provider execution and integration
evidence remain required before those paths can be marked verified.

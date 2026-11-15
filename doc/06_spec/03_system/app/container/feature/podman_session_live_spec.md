# Podman session live regression manual

Qualification: **NOT_RUN** for the 2026-11-14 command override change. No
runtime, build, or engine qualification was attempted; the parent session's
qualification iteration cap is exhausted. Source assertions are not live
evidence. An ungated green suite is not engine evidence either.

The legacy `PodmanSessionSpecV1.command` is an exact executable/argv vector.
The session builder emits `--entrypoint`, an empty argument, the image, then
the complete command vector. Clearing ENTRYPOINT prevents an image launcher
from intercepting the requested executable; retaining the executable after
the image avoids Podman's JSON interpretation of an entrypoint option value.
Podman's [run reference](https://docs.podman.io/en/stable/markdown/podman-run.1.html)
documents ENTRYPOINT replacement and command handling.

The opt-in regression scenario uses a local image whose ENTRYPOINT and CMD
are both `/bin/false`. Build the fixture when qualification is authorized:

```sh
podman build -f test/fixtures/container/podman_session_entrypoint.Containerfile -t localhost/simple-podman-entrypoint-regression:local test/fixtures/container
```

Run `test/03_system/app/container/feature/podman_session_live_spec.spl` through
the qualified self-hosted runtime with `SIMPLE_PODMAN_SMOKE=1` and
`SIMPLE_PODMAN_ENTRYPOINT_IMAGE=localhost/simple-podman-entrypoint-regression:local`.
An enabled live run without the fixture image setting fails explicitly.
The existing cases also require a local `busybox:1.36` image.

Expected assertions: `/bin/printf` returns exactly `<two words><>` despite the
failing image defaults; `/bin/printf` without arguments fails with empty stdout (a retained image CMD
would instead print `/bin/false` and succeed); a missing
executable fails; each run is reaped and the owner has no remaining containers.
The previous builder runs `/bin/false` instead, so the first assertion fails.
The unit spec additionally checks exact argv for spaces, empty arguments,
shell metacharacters and JSON-looking executable names, plus rejection before
runner dispatch for empty executables and embedded NULs.

Scope: legacy session provider and its Caret/test-runner consumers. The shared
OCI provider's existing command mapping and common Container API migration
are outside this change; this manual does not qualify either.

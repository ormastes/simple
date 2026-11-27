# BuildRunner Hello requested implicit output mode

Status: fixture fixed; diagnostic red/green verified; production admission OPEN.

The `hello_native_run_v1` fixture declares only `hello.exe`, but its compiler
argv omitted an explicit link mode. A recovered pure-Simple P2 diagnostic with
the same shape compiled and linked native Hello, then entered SMF packaging
and failed that phase on Darwin. SMF collection currently requires ELF object
code; enabling packaging does not help this native-only fixture.

This is an output-intent correction, not a claim that mode alone caused the
overall nonzero build status. The one-binary diagnostic also reported
`target-identity-error: darwin-deployment-or-sdk-missing`. Darwin callers must
provide host-derived `SDKROOT` and `MACOSX_DEPLOYMENT_TARGET`. The worker already
preserves these values in its explicit, digest-bound environment snapshot;
do not add implicit SDK discovery to the worker or relax target admission.

The regression requires explicit `--mode one-binary` and a cache key different
from the former implicit-mode task. Live manager Hello remains dependent on
qualified process ownership; direct compiler diagnostics do not satisfy it.

## Direct compiler diagnostic

Recovered P2 SHA-256
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`
compiled `test/04_smoke/bootstrap_hello_world.spl` with one-binary mode and
host-derived SDK/deployment values. Compiler exit was 0; the native artifact
printed `hello` and exited 0. Artifact SHA-256:
`26e814a05193bf54e5230672db4a12fd028a5cffb49d49d6c60d26be6015fa21`.
Logs: `/private/tmp/lunar-buildrunner-hello-sanity-20261029/build-one-binary-sdk.log`
and `hello-one-binary-sdk-run.log` in the same directory.

This is a different smoke source and direct invocation, not execution of the
BuildRunner fixture or production-worker qualification. Native admission owner:
bootstrap/runtime lane; unblock with the current manager and a qualified strict
process/memory provider, then execute and verify the declared Hello fixture.

## Fixture regression

The five-case `test/01_unit/app/buildrunner/hello_native_run_v1_spec.spl`
executed with explicit `SIMPLE_TEST_RUNNER_RUST=1`, bounded to 90 seconds plus
5 seconds cleanup. Before the fix: 3 passed, 2 failed, exit 1. After: 5 passed,
0 failed, exit 0. Seed SHA-256:
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`.
Logs: `/private/tmp/lunar-buildrunner-hello-native-run-red-seed.log` and
`/private/tmp/lunar-buildrunner-hello-native-run-green-seed.log`.
This is diagnostic seed evidence; generated manual verification and current
pure-Simple fixture execution remain open with the bootstrap/runtime owner.

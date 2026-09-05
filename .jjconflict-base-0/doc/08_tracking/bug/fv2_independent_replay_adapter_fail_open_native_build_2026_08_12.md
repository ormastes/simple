# FV2 independent replay adapter fail-open native build

## Status

Setup gate repaired; current adapter remains unavailable until a clean
pure-Simple native build succeeds.

## Observed failure

`setup-fv2-independent-replay.shs` previously accepted process exit zero from
an admitted pure-Simple compiler even though native-build reported a stale
runtime archive, generated 14 unresolved-symbol stubs, and linked a 58 KiB
adapter. It then wrote `manifest.txt`, falsely promoting that adapter into the
independent proof-replay toolchain.

The unresolved set included `str.is_alphanumeric` and OpenSSL entry points.
With `SIMPLE_NO_STUB_FALLBACK=1`, the same build fails closed at link time and
does not issue a manifest.

The adapter no longer depends on the broad `app.io.mod` compatibility hub and
uses explicit ASCII token classification instead of `str.is_alphanumeric`.
Its entry closure now names only the canonical directory, file, and process
facades it actually consumes.

## Repair

The setup owner now:

1. removes prior adapter/manifest evidence before reprovisioning;
2. builds to a temporary path with `SIMPLE_NO_STUB_FALLBACK=1`;
3. retains and scans the build transcript for stale-runtime or stub markers;
4. requires an executable output and an exact argument-gate linkage smoke;
5. atomically promotes the adapter only after those checks;
6. hashes the compiler and build transcript into the tool manifest.

The rejected adapter and manifest from the reproduced fail-open run were moved
under `build/fv2-tools/rejected/`; they are not evidence inputs.

Provisioning also now pins the format-v2 exporter fork required by nanoda,
checks a one-root positive compatibility fixture, and requires a project-axiom
root to fail. The former official NDJSON exporter pin produced format 3.1.0,
which nanoda 0.3.2 cannot parse; that combination can no longer issue a
manifest.

## Required closure

- Rebuild the current `simple-core` runtime archive.
- Resolve any remaining linkage boundary without a stub or broad hosted
  fallback.
- Re-run setup with an admitted current-source pure-Simple compiler and require
  a clean manifest plus independent replay of every release proof root.

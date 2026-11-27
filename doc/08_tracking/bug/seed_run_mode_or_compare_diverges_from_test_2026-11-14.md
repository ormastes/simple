# Seed `run` mode diverges from `test` mode on `not f(x) or a != b`

Found 2026-11-14 on macOS 26.5 arm64, seed
`src/compiler_rust/target/release/simple` (built 2026-11-04).

`seatbelt_capability_status_v1(m, build, "arm64", d)` returns
`unqualified / helper-digest-unqualified` under `bin/simple run <script>.spl`,
while the same call with the same inputs returns `qualified` under
`bin/simple test` (checked with a throwaway spec). In the run script,
`m.helper_digest == d` prints `true`, the length is 64, and every canary passed
`builder_digest_valid_v1(...)`. The failing line is
`if not builder_digest_valid_v1(manifest.helper_digest) or manifest.helper_digest != expected_helper_digest:`
(`src/lib/nogc_async_mut/container/providers/macos/seatbelt_capabilities_v1.spl`).
`run` also logs `Failed to load imported types ... resolves from the project
stdlib roots only` for the imported module, so cross-module type loading
probably degrades the comparison. Ruled out: running the same script from
inside the worktree (no import warning) still returns `helper-digest-unqualified`.

Repro: a script outside the repo importing
`std.nogc_async_mut.container.providers.macos.seatbelt_capabilities_v1.*`
that calls `seatbelt_manifest_from_probe_v1` with a full canary transcript and
then `seatbelt_capability_status_v1`. Expected `qualified`.

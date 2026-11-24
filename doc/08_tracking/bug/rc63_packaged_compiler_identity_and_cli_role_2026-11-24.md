# RC63 packaged compiler identity and CLI role

Status: open packaging/provenance issue; an authentic bootstrap compiler is
available in the SPK, but full-CLI verification remains blocked.

## Observed failure

The first guest-owner verification run
[45364574569](https://github.com/ormastes/simple/actions/runs/45364574569)
verified the official full-archive digest and arm64 runner architecture, then
failed during compiler-image identity checks. No CLI, five guest-owner unit
cases, or eight SDK observer cases executed.

The follow-up run
[45373932507](https://github.com/ormastes/simple/actions/runs/45373932507)
was cancelled while queued with no steps after source review established a
second problem: its executor required ordinary `check` from a bootstrap-only
compiler. Both allocated verification cycles remain accounted for; neither
result qualifies the production change in
[draft PR #11282](https://github.com/ormastes/simple/pull/11282).
The owned manual workflow was disabled pending a role-correct replacement.

## Immutable package identities

Release: [rc-1.0.0-rc.63](https://github.com/ormastes/simple/releases/tag/rc-1.0.0-rc.63).
Declared source: `0bf70cd733ffbe5e3acb179797d4e91e993e1eef`.
The separately published `PROVENANCE.sdn` is 1,559 bytes and has SHA256
`6be38b2093b11cab6160c63a9229ec504b244590c741fbd830a7393c4a38911c`.
It is byte-identical to the provenance record in the full tar archive.

| Asset | Bytes | SHA256 |
|---|---:|---|
| `simple-1.0.0-rc.63-darwin-arm64.tar.gz` | 396,743,315 | `0a727acb3c7f3ee5eea755bf676f9f05df987e43722f92056ee6285c6d0c1c47` |
| `simple-bootstrap-1.0.0-rc.63-darwin-arm64.spk` | 389,233,308 | `40f4c5377d276e5366081a4d8cb495a62f0eebfdedbce3afec90d339fec7735f` |

The provenance record declares both `phase3b_simple_sha256` and
`phase4_cli_sha256` as
`085796e2d83ae984884bc9d0c1a7c6f40130df6b12f9df6b5aa5c5534bd23e2d`.
Offline inspection found these physical regular files:

| Package member | Kind / bytes | Actual SHA256 |
|---|---|---|
| Full tar `bin/simple` | shell wrapper / 381 | `de2fb560a8a8384741fef7f57084a8619b376cf0a0b58de7082ce1f17dc6f285` |
| Full tar `bin/simple-runtime` | arm64 Mach-O / 19,909,120 | `27127c5e64c56c6bacae72b6e6cfcd8c218dde3015b395741a6811589128bb9e` |
| Full tar `bin/simple-bootstrap` | arm64 Mach-O / 19,909,120 | `7c898fb79394e20467c6b267cab58686c7961dfbafa5f957dabf100e2598497d` |
| SPK `bin/simple-runtime` | arm64 Mach-O / 19,909,104 | `085796e2d83ae984884bc9d0c1a7c6f40130df6b12f9df6b5aa5c5534bd23e2d` |

The full-tar wrapper dispatches `bin/simple-runtime`; it is not the compiler
image. The SPK root is `simple-bootstrap-1.0.0-rc.63-darwin-arm64`, with
`PHASE` exactly `3\n`. Its physical compiler matches the declared P3b digest.
The SPK is an ordinary gzip-compressed tar archive, as implemented by
[`package-phase1-spk.shs`](https://github.com/ormastes/simple/blob/0bf70cd733ffbe5e3acb179797d4e91e993e1eef/scripts/release/package-phase1-spk.shs).

The SPK and full tar both contain test/build tools and all five runtime
libraries matching the same published provenance:

| Component | SHA256 |
|---|---|
| `simple_test_runner` | `9fb60a3a0591d9457a77294bdb1f19f3a0f4b1597544f3b4b8d0327c236c29f2` |
| `simple_build_runner` | `f03a6fb9bc5ecdb6b50f323e874cd39550fbc3843d4354b9c623a7f0fca26b5b` |
| `libsimple_runtime.a` | `b8b93cb95b742f417a49ee8e9a09c6052d078705f5a0df16b22d5709c3b07556` |
| `libsimple_runtime.dylib` | `04fd13978d6dcf13131d69e7793cd129cf03827d2802fc237f87dafb6ccef878` |
| `libsimple_native_all.a` | `71d8ef10b966672a7a38133618bc15494f439c07a9fd5f96bb624d2ff70ca320` |
| `libsimple_compiler_backfill.a` | `83779d81de3d3fce402ddc86da7eb0b60da28525fc369c9acda3f5413c85e6dd` |
| `libspl_hosted_runtime.a` | `b893d1af8a572afe8abab1e28084cab7e9897da5f9ea1baad9e2fa106ac0c387` |

No cause for the differing full-tar compiler bytes has been established.
An undocumented signing or packaging transform is not accepted as proof of
identity. The expected digest must not be replaced with an observed digest
merely to pass admission.

## Separate command-role problem

At the declared source revision, the
[`bootstrap_main.spl` entry](https://github.com/ormastes/simple/blob/0bf70cd733ffbe5e3acb179797d4e91e993e1eef/src/app/cli/bootstrap_main.spl)
supports `native-build`, `compile --format=smf`, version/help, and allowlisted
internal workers. Ordinary `check`, `test`, `lint`, and unmarked `run` take its
unknown-command path. The
[`bootstrap-from-scratch.sh` pipeline](https://github.com/ormastes/simple/blob/0bf70cd733ffbe5e3acb179797d4e91e993e1eef/scripts/bootstrap/bootstrap-from-scratch.sh)
builds this entry for staged bootstrap and distinguishes the full CLI.

Matching the P3b image therefore authenticates a bootstrap compiler, not a
general CLI. Treating `phase4_cli_sha256` as proof of general command support
was an executor-review mistake. The queued follow-up was cancelled before
any runtime invocation; it was not a failed execution of the unit cases.

## Required correction and acceptance evidence

1. Record packaged executable paths and their final physical digests separately
   from shell wrappers. Document and authenticate any packaging transform.
2. Distinguish bootstrap-compiler and full-CLI roles. Do not alias a P3 digest
   into full-CLI admission without demonstrating the general command route.
3. Obtain an authenticated full CLI, or explicitly admit building the canonical
   full CLI from the verified P3 compiler. This need not rebuild P3 itself.
4. Verify supported `check` and fixture-child `run` behavior on that full CLI,
   then execute the actual unit and required source checks. Retain separate
   command results, expected case counts, input identities, and raw outputs.

The SPK supplies an authentic compiler for supported bootstrap/native-build
operations. It does not establish that the five/eight host controls or any of
the 24 SimpleOS guest lint/test/linker cases have run. Guest results remain
0/24 at this report's observation point.

Retained offline evidence is under
`C:/dev/simple-xc-guest-command-20261124/build/verify/guest-command-cycle1/`,
including `rc63-offline-library-identities.sdn` and
`rc63-spk-offline-roles.sdn`. The critical byte identities are included above
so this report does not depend solely on local build files.

# Frozen semantic owner standalone native fixture

Status: **NOT_RUN**. This artifact defines a diagnostic execution oracle; it is
not runtime qualification, Phase 3 acceptance, or semantic compile authority.
No builder, native fixture, SSpec runner, or test CLI was launched for this change.
Source-only checks passed: staged whitespace validation, both working/staged
direct environment/runtime guards, and zero executable specs under `doc/06_spec`.
These checks do not establish that the fixture compiles or executes.

## Session identity

- Owner: Codex Sol, `/root/impl_solver_host`, with Astra source review.
- Session: `scv-semantic-native-fixture-20261030`.
- Worktree: `/tmp/simple-scv-semantic-native-fixture-20261030`.
- Branch: `work/scv-semantic-native-fixture-20261030`.
- Exact base: `ef18c77db55698c8d9ea70b16bd4a5c3dccf014e`.
- Expected integration target: parent-owned unfinished diagnostic producer PR
  toward `release/1.0.0`, through the parent's reviewed integration flow.
- Scope: one standalone `.spl` fixture and this report; the reviewed producer
  worktree remains frozen. No push or merge is performed by this lane.

## Actual execution path and oracle

`test/fixtures/compiler/scv_frozen_semantic_owner_native_probe.spl` imports the
actual narrow driver module and calls both diagnostic APIs. It does not import
`std.spec`, route through the test CLI, mock a result, or assign inferred types.
The production path owns frozen parse, HIR lowering, strict HM checking, typed
clone production, and portable verification. Six controls increment only after
their assertions succeed:

| Control | Real input/call | Required outcome | Exit offset |
|---|---|---|---:|
| 1 | i64 tail / old diagnose | diagnosed, actual literal 42, parser/HIR/HM counts 1 | 0 |
| 2 | i64 tail / new observe | actual typed counts 1/1, `facts-only` | 30 |
| 3 | bool tail / new observe | actual true, typed counts 1/1, `facts-only` | 60 |
| 4 | explicit Return / new observe | actual literal 42, typed counts 1/2, exact verifier refusal | 90 |
| 5 | wrong bool return / old diagnose | actual HM rejection and nonempty errors | 120 |
| 6 | wrong bool return / new observe | same rejection, zero owner/body handles or verification | 150 |

The success detail for controls 2/3 is exactly
`live-attempt-pin-body-lease-required`; control 4 requires status `unavailable`
and detail `unsupported-semantics:function body`. The existing portable verifier
supports a narrower profile than the genuine HM annotation producer. Its
refusal is an assertion, not an accepted alternate success outcome.

Each call checks scratch state zero, exact source/path/module/target binding,
actual parser/HIR/HM counts, and all available semantic/full-artifact/install/
execute flags false. Successful owner calls also check the actual declaration
issue/consume/foreign/mutation/retirement observations and zero active handles.
Distinct nonzero exits identify the failed control and check. Only after all
six controls succeed does the entrypoint emit its single SDN PASS record with
`controls: 6` and `qualification: diagnostic_only`.

## Exact bytes and digests

Sources are UTF-8/ASCII with LF line endings, four ASCII spaces before the body,
and one trailing LF. The quoted representations below use `\n` solely to show
those exact LF bytes; the fixture creates the actual byte arrays through
`text_to_bytes` and independently supplies `sha256_text` in each request.

| Source bytes represented | SHA-256 |
|---|---|
| `fn answer() -> i64:\n    42\n` | `178805333df0333ba53113e123278a4795cac06ddf9f1ecada8c28776d542db8` |
| `fn yes() -> bool:\n    true\n` | `33bf1ae99a05f0ae64439b07b75a08e1002781e906218d1277c5437045cfe26c` |
| `fn answer() -> i64:\n    return 42\n` | `12706aa1234f34f30312af998a5b651e25a9e88aa5e0928cc05e1b3e3e9c241a` |
| `fn wrong() -> i64:\n    true\n` | `89f750563f93192ae4d79935673bdd8ed4bc91356e0ea2bd4fd0d553e79de66b` |

Exact fixture SHA-256:
`19022ad2f893a2dfb2439346c91d94d0f5d100fd0ccca55e624173677170fc93`.

Production source hashes at this fixture's base:

| Source | SHA-256 |
|---|---|
| `src/compiler/80.driver/driver_frozen_semantic_prerequisites_v1.spl` | `abffb9d1cc1224f9d7d4bd42a88e8840573631cc08961dcda525cf01c74c6438` |
| `src/compiler/30.types/type_infer/typed_module_owner_v1.spl` | `797f3087f9ed2619de48e279fbb8a0af32124d8842851d70eced379b02afb70d` |

## Pending execution and full-goal gaps

Root must authorize capacity and identify an actual qualified compiler/runtime
artifact before compilation or execution. The later evidence must record exact
compiler/runtime and fixture digests, command, native output artifact identity,
exit code, and captured output. No artifact identity or success is invented here.

All five semantic issuer/install/execute gates remain closed. Exact live L7
attempt/pin context, parser/preprocess ownership below the driver, retained
issuer lifecycle, and complete general-language universes remain separate
requirements. This fixture cannot authorize artifact reuse or execution.

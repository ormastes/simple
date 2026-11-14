# Top-level declaration visibility intent retention

Selected scope: [aspect and visibility plan](../../03_plan/compiler/aspect_dynload/aspect_dynload_visibility_improvement_plan_2026-10-31.md), section 1.1.

This slice records source facts needed by that plan. Ordinary `pub` declarations
form the planned feature-public surface; no `allpub` keyword is introduced.

## Interface and ownership

The canonical module parser records parallel byte-offset and modifier arrays
before its existing declaration dispatch. Each offset identifies the first
byte of an explicit modifier, or the declaration-start token when omitted.
This remains stable when an ordinary pub modifier precedes a newline.
The arrays contain top-level observations only, not member or generated entries.
Modifier codes are `omitted`, `pri`, `public`, `peer`, `up`, `internal`, `package`.
Missing observations return `unknown` and offset -1, never inferred permission.

The three `parser_top_level_visibility_intent_*_v1` readers expose count,
source-byte offset and modifier. Consumers must bind the source observation
to a real declaration within the same source snapshot before deciding scope.
The readers hide observations while the parser has an error. No module/path identity
is invented by the table, and observations are not effective access verdicts.

The existing declaration allocator, getter, member parser, typed bridge and
`pri` dispatch are unchanged. In particular, `pri static` and `pri macro` keep
their existing parser routes. The pending-metadata owner handles reset,
transient promotion, state take/install, and codec persistence of both arrays.
Restore rejects unaligned rows, unordered offsets, and unknown modifier codes.

## Cache compatibility and limits

`spl-flatpool-v17-declaration-visibility-intent` replaces v16. The existing
frontend grammar digest and phase compatibility identity include this value,
requiring older snapshots to be reparsed. Old `Visibility.Private` values are
not reinterpreted. ModuleSurface still carries its conservative typed visibility;
joining these observations to semantic declaration identity remains future work.

This is not folder-local reachability enforcement, resolved export promotion,
the public-set schema migration, or live LSP/MCP visibility. Those consumers
must adopt the same source identity and boundary rules separately.

## Evidence boundary

The SSpec at `test/01_unit/compiler/frontend/declaration_visibility_intent_spec.spl`
checks real parsing, metadata round trips, take/install, member and generated
defaults, unchanged pri static/macro grammar, missing facts and cache identity.
The production-source native probe is
`test/02_integration/compiler/native/declaration_visibility_intent_probe.spl`;
success requires `declaration_visibility_intent_cases=23 failures=0` and exit 77.
Execution and broader compiler/tooling checks are pending. Source review is not
runtime verification. Astra owns implementation; Luna reviews parser/cache paths.

## Bounded build evidence (2026-11-14)

Base: `ecb2d5059efcb2f601334e4adc59fc0b24a6c861`. The focused Stage 2 compiler
was the admitted executable under
`simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
SHA-256 `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
No Rust seed or modified production import was used.

The native-build command selected `src/compiler` and `src/lib`, the probe entry,
`--entry-closure --runtime-bundle core-c --threads 1`, with an isolated cache.
Its resolved production closure contained 153 modules. Attempt 1 stopped at
120.497 seconds, peak process-tree RSS 3,443,277,824 bytes, after entering MIR.
After source-review fixes, one authorized continuation reused that cache with
a 300-second/4-GiB bound. It completed all 153 MIR/AOP modules and entered native
code generation, then stopped at the RSS cap after 253.341 seconds, peak sampled
RSS 4,419,600,384 bytes. Both exits were -15. Sampling permits a small overshoot
before termination. No executable or runtime assertion PASS was produced.

Evidence remains under the isolated worktree's `build/visibility-intent-20261114/`:
`command_cycle2.txt`, `source_identity_cycle2.sdn`, `build_cycle2.log`, and
`build_receipt_cycle2.sdn`. The cache is retained; no further retries are scheduled.

The flat-codec completeness audit checks 163 pools after adding the two new
inline-reset observations to its oracle. It still fails on unchanged baseline
`named_type_modules` and `par_error_records`, which lack codec coverage. Running
the original guard against an archive of the exact base checked 161 pools and
reported those same two failures. This evidence does not waive the full gate.

Status: source implementation and regression artifacts prepared; runtime,
generated-manual, full compiler/tooling verification, and landing remain pending.

# MIR/codegen repair campaign — release/1.0.0

Status: in progress; no new native PASS claimed.

The user requested all MIR/codegen bugs be fixed, alongside the ongoing node
attribute implementation, and authorized a twelve-hour continuation beginning
2026-11-06 19:59 UTC. This inventory is finite and evidence-based; it does not
claim all compiler defects are known. Preserve existing source workarounds until
the affected native paths pass with a source-matched producer.

| Cause | Current evidence | Required next result |
|---|---|---|
| Nested indexed-array push AV | Existing repair `83c17508b4a` writes the call result directly into the receiver; native replay pending | Compile/run `test/fixtures/compiler/mutate_index_nested_array_push/main.spl`, including selected and sibling row checks |
| Generic method Result Ok provenance | Existing repair `5b98de2126c`; prior seed evidence is not native admission | Execute `result_payload_provenance_spec.spl` with no MIR errors and native generic-method replay |
| Result Err binder provenance | Historical Stage 2 failure 5/5; existing unit shape did not reproduce it | Compile/run `native_result_err_generic_method_payload.spl` without a typed alias, then replay actual simple_ring closure |
| Optional trait field assignment | Historical admitted Windows producer rejects trait-to-trait field copy as missing concrete implementation | Recover declared field type without reboxing the trait object; test Some, None, distinct implementation identity, and incompatible owners |
| Trait call through optional field | `self.bitmap!.reducer` declaration recovery stops at Unwrap | Preserve declared type through unwrap and use exact trait dispatch; execute native fixture and DB closure |
| MIR registry lifetime | Stored-value journaling repair exists; older by-value journal probe failed | Source-matched registry regression and self-build; do not duplicate existing source fix |
| Native struct receiver projections | Existing source workarounds/repairs; latest native qualification incomplete | Run receiver smoke fixtures with refreshed producer; keep historical failures distinct from current ones |
| Windows pre-link diagnostics | AVX loadgen report says error text lost before linker launch | Independently identify/report the linker error; this is not established as a MIR defect |

Relevant reports remain under `doc/08_tracking/bug/`; ownership is tracked by
the existing bug-claim tool. Parallel lanes own distinct source files or explicit
helper regions. No unrelated dirty changes or foreign bootstrap processes are
part of the repair.

## Execution boundary

The separate frozen bootstrap initially used
`6e03930143983a5c9861321f67aff300b07f16ed`. Attempt 6 linked a candidate but failed
frontend sanity because 9,121 MiB headroom was below the default 24,576 MiB
reserve. It is rejected, not an admitted feature-test runner. Attempt 7 reuses
compatible caches with one worker, enforced RSS limits and an explicit 4 GiB
reserve. All normal admission gates remain required. Its log is
`D:/dev/simple-node-attribute-bootstrap-20261106/build/node-attributes-qualification/bootstrap-attempt7.log`.

The independent boot2 build reported 555 failures after a 300-second
`driver_aot_pipeline.spl` timeout: one executed failure and 554 unattempted rows.
This is neither 555 MIR defects nor evidence that those rows pass.

Native fixture success from an older admitted producer diagnoses that producer;
it does not qualify newly edited compiler source. Final acceptance requires
rebuilding the affected producer, executing regressions and applicable core/MCP
checks, reviewing the exact PR diff and comments, and merging to release/1.0.0.

Attempt 7 terminated with exit 1 after reusing 1,592 native modules and rebuilding
two. Sanity rejected the default per-file pool: two 9,000,000 kB workers require
30,000,000 kB free, while the observed headroom was about 4.2 GiB. The outer
`--jobs=1` does not select that inner route. Attempt 8 explicitly selects the
supported `SIMPLE_FILE_WORKERS=0` route, preserving the 4 GiB reserve, RSS
enforcement and all admission checks. Its log is `bootstrap-attempt8.log` in the
same qualification directory; attempt-7 sanity receipts were preserved first.
This is a resource-route change, not a MIR fix or a successful test result.

Attempt 8 also terminated unadmitted: the frontend observed 3,735 MiB free,
below the 4,096 MiB reserve. Its preceding native build exited 0 with peak RSS
1,691,848 KiB and peak job commit 1,855,132 KiB. With about 33 GiB free commit
headroom, the final resource-policy retry selects a positive 2 GiB reserve;
RSS enforcement and `SIMPLE_FILE_WORKERS=0` remain unchanged. Attempt 9 did not
compile: it timed out on output ownership while attempt 8 was still cleaning
up. After both wrappers terminated, attempt 10 started with the same intended
policy. No further automatic reserve reduction is planned.

Attempt 10 stopped at preflight Git-state binding. An isolated consumer timed
out at its normal outer limit, then completed in 14m43s with its existing
20-minute ceiling. The configured budget was lost at the hermetic environment
boundary. PR #7377 landed the forwarding fix on `release/1.0.0` as
`07ed63594330bdb6ac5260318017636618cbe587`, with five executable routing cases
and applicable CI gates passing.

The isolated bootstrap now pins `08944a34d899a5beea2940b6a9688d08252e51bb`.
Attempt 11 retains the 2 GiB reserve, one worker and `SIMPLE_FILE_WORKERS=0`,
uses the existing 1,200,000 ms Git-state ceiling, and generated fresh
revision-bound materialization receipts. It passed preflight and entered
Stage 2 compilation. This is not yet self-hosted CLI admission.

## Broader ledger census and additional candidates

A read-only census of ten-column `bugs_active`/`bugs` rows selected MIR,
MIR-optimization and backend owner paths plus MIR/codegen IDs/titles, excluded
identified seed-only/vendor defects and deduplicated IDs. It found 144 active
candidates: 67 open, 74 source-fixed awaiting verification, two other
verification-pending and one fixing at census time. Severity counts were two
P0, 53 P1, 55 P2 and 34 P3. Nine non-ten-column lines were excluded. This is a
bounded ledger inventory, not 144 reproduced defects or a complete semantic
classification. Both P0 rows already record source repairs awaiting execution.

Additional work:

- Signed narrow Cranelift arithmetic now restores I8/I16/I32 sign extension
  after ordinary BinOp operations, reusing the existing unary-negation rule.
  The fifteen-check native fixture widens expressions directly so an annotated
  narrowing Let cannot mask the regression. Execution remains pending.
- Optional trait recovery now ignores only top-level Error/Infer placeholders;
  Any, concrete declarations and nested unknown optionals retain authority.
  Eleven controlled metadata cases are authored, not executed. The follow-up
  extends the release's canonical helper rather than adding a second resolver.
- The optional-Bool if-val defect remains open. Its ten-check native fixture
  covers None, false/true payloads, explicit Bool presence predicates, elif,
  and bounded while bindings. A structural candidate carries parser provenance
  through HIR lowering, resolution and union rewriting into MIR. Five codec/hash
  and three transform scenarios are authored but unexecuted. Generated codec
  and hash outputs still require the admitted self-hosted generator; the source
  candidate is not ready to merge without regeneration and verification.
- The environment-text ABI failure was re-scoped upstream to LLVM's bare
  `env_get` alias, and a source repair landed there. The native fixture now
  exercises that imported name and does not require nonexistent cross-module
  body inlining. Source-matched native replay remains pending.
- Release already implements SVM-G integer printing, floating compound
  arithmetic and signed shifts. The integrated follow-up preserves these and
  fixes result classification, rejects mixed numeric binary operands at their
  common lowering boundary, and emits checked Float-typed integer constants
  as float words. Checked helper results remain supported. The suite has 53
  authored examples, including 12 additions over the release baseline; the
  new cases remain unexecuted.

## Release integration

The branch was rebased onto `fe91477a710ada22f40249fb99b2c92ced7c92bd`.
Newer release trait-field, unwrap, link-diagnostic and SVM-G implementations
were retained; competing copies were removed. Current release bug-ledger
state was preserved instead of replaying stale ownership/status records.
The Boolean candidate requires v17/canonical-v7 because release already
uses v16/v6 for local-annotation provenance. Regeneration must use the
integrated generator, including its newer depth and ordering checks.

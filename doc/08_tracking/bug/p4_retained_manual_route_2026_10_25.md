# Retained manual Stage4 link route

Status: OPEN — native Stage4 qualification remains pending.

`@workaround bug=retained_manual_system_link_old_seed_abi_2026_10_25`

An already retained seed/runtime can have an ABI incompatible with the normal
Simple API system-link path (`rt_fd_stat_snapshot_v1`). Rebuilding that runtime
or substituting a Rust producer changes the evidence being qualified. The
explicit retained-manual route instead builds each actual tool aggregate with
the selected self-produced compiler, preserves the compiler's raw result, and
requires independently reviewed object evidence before compiling a canonical
entry shim and strictly linking the retained providers with system clang.

Related OPEN compatibility issue: `native_build_parent_artifact_observation`.
The known coordinator diagnostic reports worker exit 0 and a missing output
binary even when a valid aggregate object was published. Only that exact
diagnostic at the actual object path, completed MIR/native ledgers with zero
failed modules, an enforced and quiescent RSS receipt, and reviewed artifact
evidence can qualify raw1 for the manual route. A different error, ICE, dropped
module, missing artifact, or stale input fails. The underlying raw1 remains in
the product receipt; normal-build qualification remains `NOT_QUALIFIED`.

This workaround does not assert that the canonical linker has passed. Remove
it only after the ordinary linker path and the native Stage4 tools are proven
with the selected producer and unchanged retained runtime. A merged controller
change or passing synthetic contract tests does not establish Stage4 test,
MCP/LSP, application, database, web, or graphical acceptance.

## Explicit interface

Legacy `--stage3-self-rebuild-result`/`--stage3-self-sanity` input contracts and
default build routes remain intact. The new Stage4-only interface is:

```sh
sh "$CONTROLLER/scripts/bootstrap/bootstrap-phase-verification.shs" \
  --phase=stage4 --backend=llvm --strategy=full --profile=full \
  --compiler="$P3B" --compiler-sha256="$P3B_SHA" \
  --stage3-retained-manual-receipt="$REVIEWED_CHAIN" \
  --manual-tool-qualifications="$QUALIFICATION_DIR" \
  --manual-tool-phase=qualified \
  --stage3-original-runtime="$ORIGINAL_RUNTIME" \
  --runtime-path="$VERIFIED_RETAINED_CAPSULE" --source-root="$FULL_PAYLOAD" \
  --work-root="$PRIVATE_WORK" --cache-root="$NORMAL_CACHE" --keep-going
```

The manual receipt is mutually exclusive with legacy provenance. Its schema is
`simple-stage4-retained-manual-self-v1`; every named authority has `_path` and
`_sha256` fields. The receipt binds `inputs`, `source_map`, `fixed_p2`,
`fixed_p2_result`, `producer_product`, `producer_sanity`, `self_product`,
`self_sanity`, `runtime_snapshot`, `c_runtime_manifest`, and `toolchain`.
`runtime_path` names the original retained generation. The input manifest uses
`sha256|absolute-path` rows, not the legacy manifest order.

The source map (`simple-retained-source-map-v1`) binds original and payload
roots, exact source HEAD/tree, original physical freeze plan/status, and a
manifest of original physically present files. The complete payload's tracked
blob bytes and recursively pinned gitlinks must match the specified Git tree.
A matching HEAD, copied executable, sparse test tree, or invented source map
does not qualify a whole-suite workspace.

A product descriptor (`simple-retained-manual-product-v1`) binds the actual
producer, entry, source, runtime, object, build log/transcript/RSS, independent
qualification, actual link inputs/result and shim/link transcripts/RSS. A
sanity descriptor (`simple-retained-manual-sanity-v1`) binds actual same-binary
version result/stdout/expected bytes/transcript/RSS and native Hello product,
output, run result/transcript/RSS. The minimal NUL-argv execv launcher used by
prepared gates is accepted only with its exact reviewed source bytes and
reopened argv/transcript joins. No receipt is synthesized to impersonate an
old aliasfix schema.

The toolchain env authority binds `cc`, `nm`, `entry_template`, `sdk_settings`
as path/hash pairs, plus `sdk_path`. If actual symbols need retained archives,
it additionally binds `native_all_support` and `macos_prefix`; archives must
match the original runtime snapshot and canonical backfill/native_all order.
The provider model selects ordinary archive members and rejects strong
duplicates; final system clang links with strict undefined-symbol checking.
Having archive files does not itself select them. The retained C manifest
always contains exactly the 39 individually pinned arm64 objects.

## Actual per-tool review boundary

The four existing role commands preserve their entry, ordered source roots,
host-gpu bundle, target/default-target semantics and ordinary cache argv. Only
the output becomes an aggregate with `--emit-object --mode dynload`. The
controller's selected producer snapshot must have the selected P3b hash.

Each role retains `manual-tools/ROLE/aggregate.o` and raw evidence. Without
`QUALIFICATION_DIR/ROLE.env`, it exits 86 and leaves readiness false. This is a
review boundary, not a fake success or permission escalation. The qualification
schema is `simple-retained-object-qualification-v1`, with actual artifact
path/hash, `artifact_validation=PASS`, actual `coordinator_raw_status`,
`normal_build_qualification=NOT_QUALIFIED`, and a bound `evidence_manifest`.
The manifest must reopen the actual object, build receipt, argv, log,
transcript and RSS evidence. A reviewer must inspect those actual artifacts;
the owner never issues its own independent approval.

Resuming the same unchanged role with that reviewed receipt reuses its retained
object evidence; it does not rerun a green compilation. Only the newly generated
canonical entry shim is compiled. All 39 retained C providers remain present;
there are no hand exclusions, stubs, undefined dynamic lookup or duplicate
definition suppressions. The system link produces a separately bound real
arm64 executable. Normal producer/runtime cache admission determines hits; no
cache key or cross-producer hit is forced.

Build readiness does not replace existing role-specific probes, full-CLI source
checks, test-runner smoke, actual MCP stdio and LSP checks, essential-tools
smoke, repository inventory or expanded nested/surface inventory. Candidate
provenance records `whole_suite_status=NOT_CLAIMED`. Stage4's canonical full
test-runner mode is interpreter; `--test-execution=native` remains stage3-only.
Separate native-suite evidence must not be attributed to Stage4 interpreter
rows. Application/GUI owners still require their real runtime/capsule/display
authorities. A cached Caret artifact and its provenance, rather than
`SIMPLE_BINARY` alone, select the PTY checker artifact.

Contract tests under `scripts/check/test-stage4-retained-manual.py` use only
explicitly synthetic tiny headers and receipts. They never execute a compiler,
runtime, native artifact or fake production capsule.

First use the same command with `--manual-tool-phase=objects`. This explicit
preparation pass skips version/test/smoke gates and attempts only the four
role aggregates. It preserves actual per-role presence/raw results and outer
command receipts separately, and
always exits86 with `candidate_publication=NOT_ATTEMPTED`. It never publishes
readiness. After independent review, the qualified pass requires all four
qualification files before starting any green gates. It cannot compile a
missing aggregate: it validates retained argv/producer/runtime evidence,
then compiles only the canonical shim and links. Default legacy flow remains
unchanged. A preparation failure still preserves its actual raw evidence.

Per-function verbosity is explicitly disabled with
`SIMPLE_COMPILER_PHASE_PROFILE=0`, `SIMPLE_COMPILER_TRACE=0`, and
`SIMPLE_MIRB_TRACE=0`, matching the reviewed full-object owner. Required
unconditional MIR/native completion and actual artifact-publication ledgers
remain mandatory. This is a logging policy, not a claim that verbosity caused
or fixes a prior SIG9.

Missing hosted authority or fail-fast can leave roles unproduced. Inspect the
preparation roles.tsv and actual receipts; exit86 does not assert that all four
objects exist or qualify any object.

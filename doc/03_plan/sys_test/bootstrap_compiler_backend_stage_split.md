<!-- codex-design -->
# Bootstrap compiler/backend stage split system-test plan

1. Stage 1 records the Rust-built Simple seed identity and receipt.
2. Stage 2 preserves the existing canonical pure-Simple build and emits a valid compiler receipt.
3. Stage 3 preserves the existing canonical pure-Simple build and binds the exact Stage-2 receipt.
4. Stage 4 is tools-only, reports zero compiler files, and links exact Stage-3 archives.
5. Mutated source, interface, archive, runtime ABI, and receipt hashes fail
   before tool compilation.
6. Tooling-only and audit-full CLIs pass identical essential-tool and behavior gates.
7. Migration stays fail-fast until the prerequisite legacy PASS receipt exists.
8. Resolve and retain the exact Stage-3 compiler identity before Stage-4 tool
   construction; execute the built tool executable and validate its
   `ToolingLinkReceiptV1` against that identity.
9. Reject Rust seed, fake compiler, stale compiler, mismatched receipt, and a
   tool executable not produced by the admitted Stage-4 transaction.
10. Bind the exact sorted `RuntimeRequiredSymbolsV1` manifest to the admitted
    runtime archive and reject one independently removed symbol before link.
11. Reject hosted runtime selection, unresolved-symbol stubs, and every seed or
    fallback marker in the Stage-4 link transcript.
12. Run bounded tool `--help` and `--version` only after successful link and
    `ToolingLinkReceiptV1` validation.

## Executable contract coverage

`test/03_system/compiler/bootstrap_compiler_backend_stage_split_spec.spl`
freezes the selected stage topology, typed receipt fields, tools-only boundary,
zero-compiler-source invariant, and migration gate. Its source/document checks
are executable design-contract evidence only; they do not satisfy runtime
acceptance for REQ-BSPLIT-001..007.

## Live acceptance gate (blocked)

After one current-pipeline end-to-end receipt is admitted, replace or extend
the contract scenarios with production-runner scenarios that retain:

1. Stage-2 canonical pure-Simple artifact and receipt hashes produced by the Rust seed.
2. Stage-3 canonical pure-Simple artifact/archive/interface hashes bound to that exact Stage 2.
3. A Stage-4 tooling receipt with `stage4_compiler_files=0` and the exact
   Stage-3 archive/interface hashes.
4. Independent negative runs for mutated source, interface, archive, runtime
   ABI, producer, and receipt hashes, each rejected before tool compilation.
5. Essential-tool and behavior-equivalence results for the tools-only CLI and
   the separate audit-full CLI.
6. Exact Stage-3 compiler identity, built tool executable output, and validated
   `ToolingLinkReceiptV1`; diagnostic Rust-seed execution is labeled diagnostic
   only and cannot satisfy tool build+run acceptance.

No Rust seed, source-inspection assertion, stale CLI, or hand-authored manual
may be promoted to live Stage-2/3/4 acceptance evidence.

## Current verification (2026-08-15)

- Contract SSpec execution: **BLOCKED before parse**. `bin/release/simple`
  rejected its deployed runtime at the bounded test-ABI admission probe.
- SPipe docgen: **BLOCKED by the same admission probe**; no generated manual
  was fabricated or hand-copied.
- Rust seed fallback: **not used**; it is bootstrap authority, not an admitted
  general SSpec/docgen runtime.
- Layout gate: `doc/06_spec` contains zero executable `*_spec.spl` files.

Exact stale-runtime reproduction is retained separately at:

- System: `test/03_system/compiler/deployed_test_runner_abi_admission_spec.spl`
  invokes the production wrapper's `test --help` path and requires a normal
  exit instead of the observed signal exit 139.
- Integration: `test/02_integration/app/test_runner_env_abi_spec.spl`
  round-trips a non-pointer-shaped value through the environment facade used by
  test-runner configuration and restores the previous value.

Run each once only after an admitted candidate has been atomically deployed;
then run the backend-split contract SSpec once and docgen once. These tests do
not authorize a Rust runner or direct seed fallback.

## Exact production resume commands

Set absolute paths from the admitted Stage-4 transaction. Do not point either
variable at `bin/release/simple`, a Stage-2/3 compiler, or the Rust seed.

```bash
candidate=${ADMITTED_STAGE4_SIMPLE:?absolute admitted Stage-4 CLI required}
provenance=${ADMITTED_STAGE4_PROVENANCE:?adjacent provenance required}
test -x "$candidate"
test -f "$provenance"
. scripts/check/lib/bootstrap-stage3-provenance.shs
. scripts/check/lib/stage4-candidate-provenance.shs
stage4_verify_candidate_provenance "$provenance" "$candidate" "$PWD"

SIMPLE_LIB=src "$candidate" test \
  test/02_integration/app/test_runner_env_abi_spec.spl --mode=interpreter
SIMPLE_LIB=src "$candidate" test \
  test/03_system/compiler/deployed_test_runner_abi_admission_spec.spl \
  --mode=interpreter
SIMPLE_LIB=src "$candidate" test \
  test/03_system/compiler/bootstrap_compiler_backend_stage_split_spec.spl \
  --mode=interpreter
"$candidate" spipe-docgen \
  test/03_system/compiler/bootstrap_compiler_backend_stage_split_spec.spl \
  --output doc/06_spec --no-index
```

Each command runs once. Any admission failure, signal exit, nonzero result,
stub count, stale mirror, or receipt mismatch stops the sequence; no seed or
wrapper substitution is permitted.

## Runtime-authority audit evidence (2026-08-15)

Read-only audit of the frozen Stage-2 authority at
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority`:

- origin-before, origin-after, and admitted directory snapshots are byte-equal;
- `libsimple_runtime.a` SHA-256 is
  `dbf235a74fc15160d34781fe31760a7851ef9bc5c5d1ff1dbfa1144dfaf21b25`;
- 20 of the 21 symbols required by the canonical simple-core runtime gate are
  defined; **`rt_char_from_code` is missing** while
  `text_dot_from_char_code` is present;
- `rt_string_free`, `simple_contract_check`, and
  `simple_contract_check_msg` each have exactly one archive definition;
- no defined symbol name matches unresolved/missing stub fabrication patterns;
- the Stage-2 transcript records `SIMPLE_NO_STUB_FALLBACK=1`;
- the retained Stage-2 build log contains no hosted/stub/fallback marker;
- no Stage-3/Stage-4 provenance manifest or corrected linked artifact exists.

Verdict: **BLOCKED before link** by REQ-BSPLIT-009. Do not run tool
`--help`/`--version`, do not promote the Rust-seed-built mini tools, and do not
substitute `simple-stub`. After the runtime authority is rebuilt and admitted,
repeat this symbol audit once; only a 21/21 result may enter the exact
production resume sequence above.

# Stage 2 loses `HirContractBlock` type at optional narrowing

Date: 2026-08-14
Status: ROOT CONTRACT FIX ADVANCED; parser contract owner incomplete
Owner: canonical HIR definitions / driver entry-closure ownership
Source authority: implementation commit `cc30abb73ddc4652d8324bfa28768eda1cf4efeb`

## Failure

A fresh full bootstrap completed publication of the Rust bootstrap tuple, then
failed current-head Stage 2 with exit 1. HIR lowering inferred the narrowed
`HirContractBlock?` payload as `ANY` at two `proof_uses` field reads:

- `src/compiler/50.mir/verification_contract_bridge.spl`, function
  `verification_contract_from_mir_v1`
- `src/compiler/70.backend/backend/lean_backend.spl`, function
  `function_contract_from_hir`

Cycle 1 after the local typed-binding change reproduced a byte-identical Stage
2 failure. Inspection then found the root cause: current main imported and used
`HirContractBlock`, `HirContractClause`, their enums, and
`HirFunction.verification_contract`, but their canonical definitions were
absent from `src/compiler/20.hir/hir_definitions.spl`. They existed only in a
non-ancestor integration commit. The compiler therefore materialized the
supposed contract receiver as `ANY`; local type annotations could not restore a
missing canonical type definition.

The root fix restores the complete contract type group and `HirFunction` field
in the canonical HIR owner, lowers parser contracts while parameter scope is
live, resolves their expressions, and preserves or explicitly clears the
contract through MIR optimization constructors. The explicit payload bindings
remain as defensive type boundaries. No Rust/runtime fallback implements this
behavior.

The render-CLI continuation independently confirmed the boundary: an isolated
cycle-2 build moved the same diagnostic into a helper whose parameter was
explicitly `HirContractBlock`, proving that local narrowing was not the owner.
Cycle 3 therefore consumes the canonical definition and alias fixes integrated
through `cc30abb73ddc4652d8324bfa28768eda1cf4efeb`, rather than retaining the
disproven helper workaround.

## Retained evidence

- Restart12 render-CLI cycle 1 Stage 2 log:
  `build/restart12-render-cli-pass2/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`,
  SHA-256 `cbdb55c0fce8d12780437ddab2d51529770e101c319db5af220dbd00fc097bf8`

- Driver: `build/restart13-bootstrap/driver-cycle3.log`, SHA-256
  `ba5ffd0e101a8e40e0613b04e2d6ef84dd9cd3ffbb82330e12137d8d6f108f90`
- Stage 2 log (cycle-unique preserved copy):
  `build/restart13-bootstrap/recovery-cycle3/stage2-native-build.log`,
  SHA-256 `f09ebebcd6978097c00259caf442662329b89da65085d79d440ecb26ed0aaa27`
- Progress: `build/restart13-bootstrap/progress-cycle3.log`, SHA-256
  `12fe5dcbae46d2db398bc1c448e52a24d48d270e95c95dd4b1c0f3f56a3664dd`
- Exit status: `build/restart13-bootstrap/driver-cycle3.exit` (`2`; wrapper
  rejects unavailable Stage 4 after the Stage 2 child exits 1)

## Unblock condition

In a fresh capped verification session, reuse the published bootstrap tuple and
cache, rebuild Stage 2 once, and require both owner files to lower without an
`ANY proof_uses` diagnostic. Continue through provenance-verified Stage 3 and
Stage 4 before executing mission-critical SSpec or docgen.

## Cycle-2 follow-up: Stage 3 alias publication RSS growth

The restored HIR definitions passed Stage 2 and its sanity gate. Stage 3 parsed
all 616 unique physical sources, began HIR with the first three source
diagnostics clean, and then grew monotonically to a retained peak of 23,845,528
KiB (22.74 GiB). The run was terminated with SIGTERM before host exhaustion;
this is bounded-safety enforcement, not a passing compiler result. Attribution
to alias publication was an inference at this point, subsequently supported by
the cycle-3 plateau after physical-source-only ParserModule retention.

Root ownership is `driver_source_pipeline_parsing.spl`: the returned context
retains `unique_entry_sources`, but the publication loop copied a large
`ParserModule` value for every row in the larger alias-expanded `entry_sources`
array. The fix publishes ParserModule rows only for the retained unique source
set, constructs a lightweight alias-to-surface index for every original
entry-source spelling, and makes non-streaming HIR consume that retained index.

Retained evidence:

- `build/restart13-bootstrap/progress-verify2.log`, SHA-256
  `8b4ec7a0a9f61d09233b6d2b200032ce1388d90081219fe0e27cb6bccdea064e`
- `build/restart13-bootstrap/recovery-verify2/stage3-native-build.log`,
  SHA-256 `b2ba46409237f915099e90ecb8efc4c8ee281f9f3942dd56aeba63581444de6d`
- terminal progress milestone `exit-143`; the wrapper receipt was interrupted
  before its outer `driver-verify2.exit` file could be written.

## Cycle-3 follow-up: duplicate parser facade export

The unique-source publication probe held Stage 3 RSS at approximately
7,783,816–7,802,000 KiB (7.42–7.44 GiB) after parse completion instead of
growing to 22.74 GiB. Stage 3 then advanced
to HIR module-surface extraction and failed closed on:

`ambiguous facade export: module=compiler.frontend.core.parser_expr item=parse_int_text package=compiler.frontend.core`

`parser_primary.spl` exported every item from `asm_match_suffix` and then
exported the same four names explicitly. Removing the redundant wildcard keeps
the explicit public surface and gives every facade item one origin. The final
source fix also restores the compact alias registry that the physical-source-
only probe had temporarily omitted.

Retained evidence:

- `build/restart13-bootstrap/progress-verify3.log`, SHA-256
  `c21400ad76239806423e3ae623c4268a46a7fed356235e9ef16da291a912d0e0`
- `build/restart13-bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`,
  SHA-256 `91041ad82dced41f6a96356e442c5404d6c7d2e1873e5508bacd40c912a6880e`
- `build/restart13-bootstrap/driver-verify3.log`, SHA-256
  `31a25cd68f41c5bfd962a164d7140df6cb933ba4d6ac1b7a645c88218d628a62`
- wrapper exit status `1` in `build/restart13-bootstrap/driver-verify3.exit`.

The fresh continuation exhausted its three-cycle cap. The next verification
must confirm the facade error is absent and complete Stage 2/3 sanity under a
current authority before promoting an admitted Stage 4 compiler.

## Current authority prerequisite

After `cc30abb` rebased over Rust packed-byte changes, the current LLVM
seed-input fingerprint became
`b02cad2d9e6135010cf99a931ba816575d310c5b7fe4cb0be2ccd4fad8d281fb`;
the published stamp remains
`69872b0a70dbefe456b99b8273d9d2747748a7457f65029b6e9e8e8b051b12bd`.
A `--pure-simple --full-cli` continuation therefore fails closed on stale
compiler backfill before Stage 2. A pure-Simple Stage 2/3 probe without full CLI
would remain diagnostic-only because provenance rejects the stale seed stamp.
The exact authoritative resume is the fresh-session, uncontended
`--full-bootstrap --full-cli --deploy` transaction recorded in the canonical
system-test plan. No fourth bootstrap was run in the exhausted session.

## Render-CLI continuation: parser contract frontier

The isolated render-CLI cycle 3 consumed the canonical HIR contract definition
and cleared both `proof_uses` diagnostics. Stage 2 then failed on one later,
more precise owner:

`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl: hir:
Unsupported feature: cannot infer field type while lowering
HirLowering.lower_verification_contract: struct 'ANY' field
'decrease_measure'`

Inspection proved `ParserFunction.contract`, `ContractBlock`, and
`ContractClause` are consumed by current HIR lowering but are absent from the
canonical `src/compiler/10.frontend/parser_types.spl`. Historical integration
commit `5958de7d4c7` contains the complete intended typed-AST contract surface,
flat-AST contract extraction, and constructor propagation; it must be ported
selectively onto current main rather than cherry-picking that broad historical
WIP commit or suppressing contract lowering.

The render-CLI session exhausted its three verification/fix cycles after this
diagnostic. Exact next verification is the retained Stage 2 command transcript
with a new isolated cache rooted beside
`build/restart12-render-cli-pass2/stage3/x86_64-unknown-linux-gnu/stage2-native-cache-cycle3`.
Require the `decrease_measure` frontier to clear, a produced Stage 2 executable,
and its sanity receipt before continuing to Stage 3. Do not replace the missing
typed parser owner with `Any`, drop verification contracts, or reuse a stale
cached object.

## Fresh continuation: typed parser owner restored, Phase 3 still blocked

The next bounded continuation selectively restored the typed parser-contract
surface and propagation from `5958de7d4c7` onto current main. It also restored
the contract statement tags and parser recognition rather than treating
contract clauses as executable body statements. A fresh Stage 2 build then
completed 858 compiled units with zero failures. Its diagnostic compiler is:

- path:
  `build/restart12-render-cli-pass2/stage2-cycle5/x86_64-unknown-linux-gnu/simple`
- SHA-256:
  `e3ae9475088ed2fe8edceb4e14f8b2db336ad8db8920d516d3dc8f99c6cf3dfc`
- sanity: version, bootstrap frontend smoke with bootstrap disabled, and the
  same smoke with bootstrap enabled all exited zero; the hash stayed stable.

That artifact is diagnostic only. It has no wrapper-owned admission manifest
or provenance and must not be copied into a canonical Stage 3 location.

The first Phase-3 attempt proved the former `ANY` and contract-tag declaration
failures absent, then reported fourteen instances of:

`bootstrap MIR lowering: cannot derive module constant type from folded value;
add an explicit annotation`

Adding explicit `i64` annotations to all six new cross-module contract statement
tags was insufficient: the fresh-cache Phase-3 retry reached the same normalized
failure and emitted no executable. Retained evidence:

- log: `build/restart12-render-cli-pass2/stage3-cycle6.log`
- log SHA-256:
  `a23ef0832fcd1644943897a72708004c2022a8b98da250f92f65442791fbcb05`
- output assertion:
  `build/restart12-render-cli-pass2/stage3-cycle6/x86_64-unknown-linux-gnu/simple`
  absent

The continuation exhausted its three-cycle cap. A fresh lane must first enhance
or otherwise inspect `MirLowering.lower_constants` in
`src/compiler/50.mir/_MirLowering/function_lowering.spl` so the diagnostic
identifies each constant name/span, then type the actual owners and rerun only
Phase 3 in a new cache. Once that succeeds, the only supported admission route
is the complete wrapper-owned LLVM transaction recorded in the canonical
render-performance plan; the diagnostic Stage 2/3 artifacts cannot be promoted
retroactively.

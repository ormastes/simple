# Seed codegen vs seed interpreter divergence: enum payload comparison (2026-10-12)

## Symptom

The SAME compiler sources, executing the SAME program, disagree depending on
whether the self-hosted compiler was **seed-natively compiled** (the matrix's
`compiler.snapshot`) or **seed-interpreted** (an in-process probe driving the
compiler's own parse/HIR/MIR functions under the seed interpreter):

- `compiler.snapshot` native-build of
  `src/lib/nogc_sync_mut/rt_hal/parallel_executor.spl` (full --source set,
  --emit-object, cranelift): **27 `unresolved method call` errors** (the
  `_fn` fn-typed-field family).
- The in-process interpreted probe over the identical module: **0 errors**.
- Same for the `SdnValue.Dict/Array` payload-mismatch family in
  env_access/plan_sdn: 12 native errors vs 0 interpreted.

The snapshot binary was seed-compiled from sources byte-identical to the
probe's. This is therefore a **seed-codegen bug**: the Rust seed's native
codegen miscompiles some function in the compiler's method-lowering /
enum-payload-comparison path. The interpreted execution of the same code is
the correct reference.

## Minimal differential repro

`src/app/sdn_diff_repro/main.spl` (13 lines) + the existing
`src/lib/common/sdn/value.spl` (imported) + the existing
`src/lib/common/sdn/parser.spl` (imported, UNUSED symbol):

```
use std.common.sdn.value.{SdnValue}
use std.common.sdn.parser.{parse_untrusted}   # <-- the flip

fn build() -> SdnValue:
    var fields: Dict<text, SdnValue> = {}
    fields["k"] = SdnValue.Null
    SdnValue.Dict(fields)

fn main() -> i64:
    val v = build()
    0
```

Exact commands (from any worktree at current sources):

```
SNAP=/Users/ormastes/wt/release-phase3/.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/compiler.snapshot
SEED=/Users/ormastes/wt/release-phase3/src/compiler_rust/target/bootstrap/simple

# Native side: FAILS — 4x "enum construction '...SdnValue.Dict/Array':
# payload type mismatch at 0", rc=1
SIMPLE_BOOTSTRAP=1 $SNAP native-build src/app/sdn_diff_repro/main.spl \
  --emit-object --backend=cranelift --threads 1 --mode dynload \
  --runtime-path <repo>/src/compiler_rust/target/bootstrap -o /tmp/repro.o

# Interpreted side: ACCEPTS, rc=0
$SEED src/app/sdn_diff_repro/main.spl
```

## Order-dependence evidence (the flip)

The failure is governed purely by WHICH modules are in the closure —
a registry/symbol-order dependence, exactly the signature of a raw-SymbolId
comparison site fed by seed-natively-miscomputed ids or metadata:

| consumer imports | native result |
|---|---|
| `sdn.value` only | PASS (0 errors) |
| `sdn.value` + `sdn.encode` | PASS (0 errors) |
| `sdn.value` + `sdn.parser` (unused symbol) | **FAIL (4 errors)** |
| `sdn.value` + `sdn.structural_scalar_value_v1` (parser's dep) | PASS |
| verbatim copy of env_access/plan_sdn.spl | FAIL (4 errors) |
| synthetic 15-struct/6-enum/10-fn module instead of parser | PASS |

A synthetic module with MORE declarations than parser.spl does NOT trigger
it — the trigger is specific to parser.spl's content (1000+ lines, tuple
payloads `Result<(SdnValue, [SdnIssue]), text>`, `Dict<text, SdnSpan>`
fields), not raw declaration count.

## Root-cause hypothesis

`enum_payload_local_compatible` (enum_constructor_payload.spl) decides in
this order: (1) `find_local_hir_type` remembered-type comparison (with the
#3156 alias-aware fallback), (2) expression-type recovery, (3) MIR-type
evidence — which for `Dict`/`Array`-typed payload slots has NO container
fallback (`case _: return false`). Hypothesis: on the seed-NATIVE lane the
remembered-HIR-type registry (the `local_hir_type_ids/values` parallel-array
scan in mir_lowering_types.spl) returns nil or a corrupted entry for the
`fields` local — e.g. the seed codegen miscompiles the array-scan or an
earlier `remember_local_hir_type` write — pushing the check onto path (3),
which rejects. On the interpreted lane the registry reads back correctly and
path (1) accepts. WHICH locals get corrupted is data/layout dependent,
explaining the closure-size flip. The #3156 alias fix worked around the
interpreted-visible half but cannot fix a native-lane registry corruption.

Next diagnostic step for the seed lane (NOT done here per lane ownership):
compile the self-hosted compiler with an eprint inside
`enum_payload_local_compatible` dumping which path fires
(`find_local_hir_type` hit/miss + both rendered types) — native vs
interpreted — on this exact repro.

## Second symptom site (2026-10-12 r10 cycle): self-name resolution inside the declaring module

The r10 lane cycle's matrix (snapshot built 06:58 Oct 12 — VERIFIED to
include #3225: the same binary compiles the `sdn_diff_repro` 13-liner with
ZERO payload mismatches, so the enum-payload MIR-evidence fallback works
natively) shows 7 errors, ALL at `src/lib/common/sdn/value.spl:48` in the
test_runner closure:

- `undefined variable SdnValue at :48:9` — the enum's OWN NAME fails to
  resolve INSIDE its declaring module.
- `unresolved method call: Float at :48:9` (span misattributed to the
  `SdnValue.Float(f)` static-fn body at line 48).
- 4x `SdnValue.Array/Dict: payload type mismatch` + 1x B5b multi-wildcard —
  the cascade from the failed self-name resolution.

The SAME binary compiles `sdn/value.spl` cleanly in the repro closure. The
failure is therefore UPSTREAM of the #3225 fallback (which is confirmed
working natively): closure-content-dependent self-name/surface resolution
inside the declaring module — matching this doc's signature exactly
(closure-specific content flips native-lane registry/symbol state; the
interpreted lane is unaffected).

This is the second confirmed symptom SITE of the one divergence: (1) enum
payload comparison metadata (original repro), (2) enum self-name resolution
in-module (this cycle). Both are decision points reading name-keyed or
id-keyed registries that the seed-native lane corrupts data-dependently.

## compiler_cli_build status this cycle

The cli row showed 0 [ERROR] lines and NO crash-signature line; it was
killed mid-HIR (1576/2534 modules) by the cycle verdict after the runner
row failed. The 2026-10-12-040049 cranelift shard crash (doc:
cli_cranelift_shard_crash_module_2026-10-12.md) did NOT recur — inconclusive:
either cleared by interim divergence-adjacent work or simply not reached
before the kill. Track on the next full cycle.
## Linux release_phase3 follow-up (2026-10-16)

The canonical Stage 2 test-runner build reproduced the `SdnValue.Array`
payload mismatch at `src/lib/common/sdn/value.spl:54` with producer
`5571bd354b42baf112cef648b6fee15fbe0997c3c9a0e1f409a6dd7e6067be6a`.
Qualifying the `SdnValue` match patterns removed the independent B5b duplicate
wildcard diagnostic, but allowing a negative remembered-HIR comparison to fall
through to canonical MIR evidence did not admit the array payload: the MIR
carrier lacks sufficient enum identity. A second call-site recovery attempt
crashed the staged compiler during MIR after 64/265 modules and was reverted in
`fd88fb91edf`. No semantic fix is admitted; the original fail-closed behavior
remains the required baseline.

## Scope note

Both matrix families from 2026-10-12 (48 rt_hal fn-field + 12 SdnValue) are
expected to be this one divergence; the 2026-10-11 hmac/TransferOut batches
predate it and were genuine source fixes. Do NOT "fix" matrix errors by
patching sources against the snapshot's behavior until the seed lane
root-causes this — the interpreted lane is the semantic oracle.

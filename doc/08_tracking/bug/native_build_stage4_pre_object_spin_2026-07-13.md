# Native-build Stage 4 dispatch and strict-link blockers

## Status

Dispatch fixed; strict Stage-4 link blocked. The earlier quadratic entry-closure
scan and canonical Rust-seed dispatch bug are fixed. A fresh bounded build now
emits every object and fails honestly at the unresolved-symbol gate.

## Reproducer

Run the Rust seed only as the bootstrap interpreter, with a fresh cache:

```sh
. scripts/setup/platform-detect.shs
PLATFORM="${PLATFORM_TRIPLE}"
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 \
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/bootstrap \
src/compiler_rust/target/bootstrap/simple \
  native-build --target "${PLATFORM}" \
  --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 4 --mode dynload \
  --entry src/app/cli/main.spl \
  --cache-dir build/native_probe/cache_stage4_targeted_4t \
  --runtime-path src/compiler_rust/target/bootstrap \
  -o build/native_probe/simple_stage4_targeted_4t
```

`PLATFORM` must be the triple returned by the canonical bootstrap platform
detector; it is intentionally not hardcoded in the command or script.

## Evidence

On 2026-07-13, a refreshed seed first exposed a parser recovery false positive:
valid Simple binders named `function` were rejected as TypeScript declarations.
The detector now requires an identifier lookahead, parser advancement reliably
buffers that token, and four focused Rust parser tests pass. A higher-capability
review accepted the Rust/Simple parity and focused Simple spec.

After that fix, a one-thread probe entered direct bootstrap discovery and found
1,043 modules, but its measured rate projected 19--20 minutes and exceeded the
900-second bound. It was stopped without loss because it had not emitted an
object. The four-thread retry reused no unproved objects, discovered the same
1,043 modules, compiled all 1,043 real object files with zero compile failures,
and preserved them in `build/native_probe/cache_stage4_targeted_4t`.

The strict link then failed with 120 unique undefined symbols: 102 `rt_*`
runtime/optional-provider symbols and 18 non-runtime Simple symbols. Inspection
of the automatically selected Stage-4 `libsimple_native_all.a` and its adjacent
runtime archive found none of those 120 definitions. The non-runtime group
includes imported-call/closure owners such as `run_check`, `run_arch_check`,
`json_serialize`, memory-debug helpers, and design-system helpers.

A final cache-preserving hypothesis check explicitly requested
`--runtime-bundle rust-hosted`; policy rejected it because that removed bundle
is not valid for `src/app/cli/main.spl`. Stage 4 already auto-selects its
authorized native-all artifact, so the flag was removed and no source or test
change was retained. No fourth build was launched after the mandatory
three-cycle cap, and no compiler or host-GPU PASS is claimed.

The earlier pre-dispatch spin exceeded the closest retained successful full-CLI
reference: 1,177 modules compiled and linked in 229.2 seconds. The fixed closure
walker itself completes about 498 files in 2.199 seconds, so CPU activity alone
was not evidence of healthy closure discovery.

## Root cause and mitigation

The seed dispatch treats a host `native-build` without `--target` as a
pure-Simple tool request and interprets `native_build_main.spl`; it does not
enter the Rust bootstrap builder. Existing retained evidence shows that adding
`--target x86_64-unknown-linux-gnu` starts discovery in seconds and completes
a 1,019-file build in 244.2 seconds.

The canonical seed Stage-4 branch now invokes the actual `native-build` command
with `--target "${PLATFORM}"`, using the already detected host triple rather than
a hardcoded architecture. The bootstrap fallback-policy integration spec locks
both the command and target into the seed branch. Instrumented verification
proves that mitigation converges through object emission.

The remaining fix belongs to two explicit owner classes, tracked by TODO 535:

1. Rebuild or correct the authorized Stage-4 hosted runtime/native-all artifact
   so required C and optional runtime owners are present without reopening a
   removed application runtime bundle.
2. Correct full-CLI entry-closure/import qualification or code generation for
   the 18 non-runtime Simple definitions.

Focused follow-up split the non-runtime group into 15 import/closure failures
and three lowering failures. The first shared import-map defect was an obsolete
blanket exclusion of every path containing `check.spl`; it suppressed the real
`cli/check.spl` and `cli/arch_check.spl` owners even though both were discovered
and compiled. The exclusion is removed, and the focused production-filename
import-map regression passes. This proves the owner fix for `run_check` and
`run_arch_check`; the strict full-CLI link has not been rerun, so the remaining
symbol count is not inferred or promoted to PASS.

The next shared closure defect was bare package facades such as
`lib.common.json.__init__`: native entry-closure discovery did not select the
cfg-active sibling that owns a bare exported name, and the re-export index used
the `__init__` file prefix rather than the package prefix. Discovery now selects
sorted, cfg-stripped AST providers with explicit export ownership preferred over
a unique implicit sibling definition, rejects ambiguous ownership, and queues
only the selected providers. Import indexing resolves direct and forwarded
owners to the parent package prefix through a deterministic fixed point; a
qualified import no longer falls back to the first global same-name candidate.
One adversarial regression executes and passes with a same-name reachable decoy,
wrong-architecture definitions, an unrelated sibling, and a two-hop forwarded
owner. Higher review rejected an intermediate first-candidate/stale-map form;
the accepted owner-set form publishes only final singleton mappings. Named
facade exports through sibling glob forwarders are queued without claiming
every name before indexing; a truly bare package `export *` now fails explicitly
instead of producing an incomplete closure. Final higher review passes. Both
direct-runtime guards pass and no direct `rt_*` use was added. The
strict full-CLI link remains deliberately unrun under the three-cycle cap, so
this is focused closure evidence rather than a compiler or QEMU PASS.

The next shared closure defect was a traversal boundary: both entry-closure
discovery and native import indexing inspected only module-level statements,
so a valid `use` nested inside a function or expression block could be parsed
and lowered to HIR but its owner never entered the native project. Both paths
now share one recursive AST walk that includes declaration bodies, statement
blocks, and expression-owned blocks. A synthetic regression places the import
under `if -> let -> lambda -> do-block`. Higher review rejected the first
partial visitor, the final bounded fix cycle closed its concrete declaration,
statement, metadata, macro, and expression carriers, and the expanded regression
passes 1/1. Final higher review passes the executable traversal and confirms
that the remaining pattern/type/signature metadata cannot hide a lowered nested
`use`. Function-local aliases still share the module-wide native use map,
so conflicting aliases in different functions remain open under TODO 556
instead of being hidden by this closure fix. The working-tree direct-runtime
guard passes and no source-level import hoist, direct `rt_*`, or symbol hardcode
was introduced. The strict full-CLI link remains unrun.

Reuse the preserved 1,043-object cache only after one of those owners changes,
then run one bounded strict-link verification. Do not add stubs, relabel a
runtime bundle, hardcode symbols, or substitute the Rust seed as production
evidence.

Related:

- `doc/08_tracking/bug/native_build_entry_closure_quadratic_hang_2026-07-12.md`
- `doc/08_tracking/bug/cpu_simd_direct_fill_full_bootstrap_stage4_spin_2026-07-08.md`
- TODO 548

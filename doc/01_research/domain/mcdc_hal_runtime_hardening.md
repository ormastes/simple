<!-- codex-research -->
# Domain Research: MC/DC and HAL Runtime Hardening

## MC/DC semantics

The FAA distinguishes unique-cause, unique-cause-plus-masking, and masking MC/DC. Unique-cause holds all non-target conditions constant; masking permits their changes only when they cannot influence the decision. Strongly coupled occurrences can make strict unique-cause impossible. Clang similarly models independent influence with other conditions fixed or masked by short-circuit evaluation.

Sources: [FAA DOT/FAA/AR-01/18](https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/AR-01-18_MCDC.pdf), [Clang source-based coverage](https://clang.llvm.org/docs/SourceBasedCodeCoverage.html).

LLVM associates decision regions with branch regions and represents observed test vectors with bitmaps. Vector space can grow exponentially, so production tools impose condition/vector limits and explicitly warn/exclude decisions exceeding them. Simple must report gross, eligible, and excluded denominators rather than silently treating an oversized or uninstrumented decision as covered.

Source: [LLVM coverage mapping format](https://llvm.org/docs/CoverageMappingFormat.html).

## Zero and bounded overhead

True static-off zero overhead requires compile-time absence of probe sites, runtime references, metadata, allocations, and logging. Linker garbage collection helps remove unreachable sections but is not a substitute for verifying emitted IR/symbols and artifact size. Dynamic instrumentation always has some dispatch/code-cache cost; disarmed patchable probes can minimize it but cannot honestly be called identical to omitted instrumentation.

Sources: [GCC optimization/link section options](https://gcc.gnu.org/onlinedocs/gcc-12.1.0/gcc/Optimize-Options.html), [Intel Pin user guide](https://software.intel.com/sites/landingpage/pintool/docs/98484/Pin/html/index.html), [SystemTap probe overhead model](https://sourceware.org/systemtap/man/stapprobes.3stap.html).

Recommended three-mode terminology:

- static-off: no probe sites or payload;
- static-on: direct compact event/bitmap updates;
- dynamic: disarmable patchpoints plus lazy aspect loading, with no aspect buffers/logging before arming.

## Provider matrices and environment replay

Embedded HAL ecosystems use common interfaces with real, mock, and alternate implementations. Zephyr Twister expands tests over platform/toolchain/capability matrices and retains filtered instances with reasons. QEMU deterministic replay records nondeterministic inputs and injects them at ordered checkpoints.

Sources: [Embedded Rust portability/HAL](https://docs.rust-embedded.org/book/portability/), [Zephyr Twister](https://docs.zephyrproject.org/latest/develop/test/twister.html), [QEMU record/replay](https://www.qemu.org/docs/master/devel/replay.html).

For Simple, one typed instruction stream should describe clocks, environment reads, files, processes, sockets, randomness, interrupts, MMIO, and DMA. Each event needs sequence, request, result/error, capability, and nondeterminism token. Providers must reject missing, extra, or reordered interactions. Effectful work requires one authority plus shadow/replay providers; only isolated pure/provider work may execute concurrently.

## Reasoned exclusions

KTAP distinguishes SKIP, TODO/XFAIL, TIMEOUT, and ERROR. Zephyr further distinguishes filtered/static inapplicability, not-run, blocked, skipped, error, and failure, while retaining reasons in machine-readable plans.

Sources: [KTAP specification](https://docs.kernel.org/5.17/dev-tools/ktap.html), [Twister statuses](https://docs.zephyrproject.org/latest/develop/test/twister/twister_statuses.html).

The suitable taxonomy is `unsupported-capability`, `unavailable-fixture`, `platform-inapplicable`, `safety-prohibited`, `nondeterminism-uncontrollable`, and `known-defect`. Every exclusion needs stable code, human reason, predicate/evidence, owner or issue, and review/expiry. A known defect should remain uncovered unless an explicitly selected safety policy permits a temporary waiver.

## Candidate budgets for selection

- Static-off: emitted hot-path code and coverage symbols/sections identical; binary text/data delta 0 bytes.
- Static-on: median time <=5%, p95 <=10%, peak RSS <=5% over baseline.
- Dynamic-disarmed: median/p95 <=1%, peak RSS <=1%, no loaded coverage pack or allocated event/log buffer.
- Dynamic-armed: median <=25%, p95 <=35%, peak RSS <=15%, with bounded vector and log buffers.
- Correctness: 100% eligible MC/DC, zero unexplained exclusions, deterministic normalized provider results/traces, and no stale/unknown skip record.
- Mission-critical runtime: zero dynamic allocations after an explicit initialization boundary; fixed-capacity overflow is a typed fail-closed result, never implicit growth or dropped evidence.

## Assurance migration

Default-high assurance is safest when absence of a declaration cannot silently choose a weaker mode. A staged interface migration should first warn with operation and caller locations, then become a compile/check error at a selected milestone. Explicit lower classification must carry rationale and must not be accepted for operations required by a mission-critical caller.

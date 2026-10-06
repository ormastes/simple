# Retained Phase3 access violation before first module function prescan

Status: OPEN; cause unproved; no compiler fix or native workaround qualified.

## Actual reproduction

Packet `p3-explicit-fold-cae5-p29232-j40` used producer SHA256
`9232bda90661f23cfd70f62a44bb65537dadf5a487c2664f721f536e507b0f74`
from source `3ba726489314888f4b0b91b7798ea7d67f804c06`, compiling authenticated
source `cae5b490ae2049d8da7bdd261fb1108f5dfa4f34` with retained HIR,
40 requested jobs and the separately recorded diagnostic Any-checker skip.

All 1144 HIR modules completed. Monomorphization reported 47 generic functions,
263 call sites, 28 specializations and **0 unresolved sites**, ending at
815440 ms. This proves only that this source-workaround workload passed that
stage; the callback inference compiler repair remains independently unverified.

MIR started at 815441 ms. The first module marker appeared at 1059630 ms:
`idx=0 module=app.cli.bootstrap_main`. Native worker 10716 then exited with
`0xC0000005` (shell 139). No executable was produced. Overall compile time was
2382.354656 seconds; peak tree RSS was 13557160 KiB. This is separate from the
earlier Any-checker crash: that checker was skipped in this run.

## Closure and retained evidence

Evidence root is
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004`.

- Request SHA256: `a945855dfc14bae2d8962c4a2aa523357a1d21c9be109897db7bfe29cec9566f`.
- `p3-cae5-mir-crash-authentication.json` verifies complete/child-exit outer
  collection, raw/native exit 1, no remnants or cleanup, request parity,
  released reservation, closed writer lease and absent output binary.
- Native RSS receipt is complete, exit 139, quiescent 1, observer errors 0.
- Root independently recorded `p3-cae5-terminal-root-review.json`.
- Raw worker stderr `native-build-stderr-9572-2.log` SHA256:
  `7469d4fd63539e9ba52eb151c0627461441ee02260a2558c3414fea4535b626f`.
- Earlier stderr `native-build-stderr-9572-1.log` SHA256:
  `abcf49096b28e43d539d13087e98b10a927205a5aadf8f0330ed811edb3d7b61`.
- Compact diagnostics retained four events without dropped or truncated events.
- `p3-cae5-existing-crash-evidence.json`: bounded existing Windows event/WER
  inspection returned no matching evidence. This is not proof that no dump
  exists elsewhere. No debugger attachment or dump generation was performed.

## Source localization and limits

In the producer's `driver_pipeline_lowering.spl`, the per-module marker
precedes retrieval of the HIR module, assignment of `direct_lowering.symbols`,
and `lower_module_transient_scoped(module, all_providers, is_entry)`.
The preceding all-module metadata prescan accounts for a separate stage;
elapsed time alone does not identify its internal bottleneck.

`module_lowering.spl` enters the transient scope and reverse-reference batch,
then calls `lower_module`. Before function lowering, that method prepares
callable links, local metadata, provider classes/methods, global storage and
other registries. `SIMPLE_COMPILER_PHASE_PROFILE=1` enables the existing MIR
trace. A streaming count over the complete final stderr log found zero
`[mir-prescan-module]` and `[mir-prescan-function]` markers (the former is
emitted with `eprint` immediately before function-body prescanning), and zero
function-lowering markers. This suggests a failure before that boundary but
does not exclude trace delivery or compiled-code defects. No specific function,
provider, metadata collision warning or memory-lifetime cause is established.

## Smallest next diagnostic and acceptance

Do not repeat the full unchanged build. Rank already-failed old vertical
entries by closure size and compare the same first-module signature. A smaller
old-producer crash is only a candidate reproducer, not proof about producer
9232. Prefer one admitted, cached, emit-object build of the smallest relevant
entry with existing profiling; keep source/producer/cache identities honest.

If that does not localize the fault, add bounded phase markers around actual
module setup boundaries in a separately reviewed compiler candidate, then use
an actual `lower_module_transient_scoped` harness with real provider modules.
Vary empty versus record/method/global-bearing providers and entry ordering;
assert emitted MIR, clean closure and repeated-module owner isolation. Do not
replace real lowering with stubs or disable validation/arena safety as a fix.

Required eventual proof: reproduce the fault, qualify a scoped repair on the
reproducer and neighboring ownership cases, then complete the original P3
workload. Memory and time must be recorded. All new native checks are UNRUN.

# Phase 2 Result byte/structured-error payload native crash

Status: OPEN. Root cause unproved; bounded diagnostic campaign exhausted.

Producer: pure-Simple Phase2 SHA256
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`,
LLVM Windows MSVC, matching frozen runtime capsule/core-c-bootstrap bundle.
Current tooling owner: `D:/dev/simple-tooling-phase2-check-20261026`.

## Minimal retained contrast

- `test/fixtures/compiler/phase2_result_byte_codec/result_payload.spl` wraps
  a byte array and a structured error through Result, maps the error into a
  second enum, and checks the real resulting byte sum/offset/reason.
  Native build exits139 after one-module MIR completion and before object
  emission. No assertions executed. Peak RSS75392 KiB; enforced cap6GiB.
- `direct_payload_control.spl` uses the same direct byte values and structured
  enum error without Result wrapping. Native build/link exit0; executable
  prints PASS and exits0 after3 actual assertions (byte sum131, offset7,
  reason invalid byte). This proves these direct payload operations, not the
  Result path or universal aggregate correctness.

Evidence: `build/tooling-phase2/result-owner-probe/{run,control-run}/`, original
fixtures and control.exe in that directory. Each build has a separate cache,
bounded collector and process-tree RSS receipt. No guard was disabled.

This is not a controlled attribution to a particular compiler function or to
Result alone: the fixtures also differ in helper calls/matching topology.
The contrast narrows the failure to that composition, independently of the
93-module SSpec wrapper generator and286-module general runner, which also
crash at MIR entry. Shared text-I/O consumers additionally diagnose Codec
payload mismatch and array values inferred I64. Their common root is plausible
but remains unproved; keep all failure families visible.

## Required repair/removal evidence

Repair the actual compiler owner or introduce a justified source workaround;
do not discard error fields, flatten errors to strings, replace byte arrays
with placeholders, or suppress failed matches. The original Result fixture
must naturally compile/link and execute its3 assertions. Then run the actual
text-I/O fixtures, canonical SSpec generator/runner and affected MCP/LSP/T32
consumers with truthful executed-case counts. The direct control already passed
and must not be replayed unchanged as a substitute for those criteria.

Shared runner/compiler campaign: initial runner, traced runner, production
wrapper generator, materialized generator, minimal Result probe, direct control
=6 accounted attempts. Preserve artifacts; additional repair/build cycles
require explicit extension under AGENTS.md. None is started by this record.

## Astra-guided renewed evidence

Under the user's renewed agent-completion instruction, root ran three bounded
diagnostic cycles with Astra guidance. Original1ad tracing still crashes139
after module MIR completion. Alternate admitted pure-Simple Phase2 SHA
17d1a40abc390c08c05cec3ba13db41eb12ee5709126c6636fe974f753f7e5ac
passes fresh Hello compile/run but the unchanged Result fixture also crashes.

LLDB captures exception0xc0000005, null read at address0x7ff74f4aae60,
instruction movq(%rax),%rdi. Static byte fingerprint
488b38ba734a6e0e41b80253d290 is unique in that exact executable at file offset
0x6fa260, RVA0x6fae60, unwind function range0x6fad40..0x6fb25e.
Its recursive depth guard and unresolved-enum string fingerprint identify
mir_verify_type_unresolved_reason in the preserved source's mir_verify.spl.
The crash is a missing MirType receiver dereferenced before kind matching.
No PDB/export symbols were available; attribution uses the exact binary's
instructions, function range, referenced strings and preserved owner source.
Origin of the missing child type and full valid-Result repair remain unproved.

This supersedes speculation that diagnostic record iteration caused this
particular fault. The compiler owner is replacing that speculative edit with
a focused verifier guard and mandatory missing-carrier error policy, reviewed
by Astra; source edits still require a rebuilt compiler and real fixture/suite
execution before acceptance. LLDB exit0 is debugger success, NOT compilation:
the compiler stopped on a fault, and no output executable exists.
Evidence: build/tooling-phase2/astra-alt/result-debugger-ready/.

## Reviewed verifier source repair

The speculative diagnostic-loop change was removed. The actual owner now
checks missing carriers before dereferencing and reports mandatory MIRV-001n.
Binary/default and SDN rule registries agree; wildcard/named off or warning
and driver warning-phase cannot admit this structural defect. Result/Tuple
walks prioritize a missing sibling over an earlier suppressible unresolved
reason (Astra caught and required this P1 masking fix). Actual module/driver
SSpec additions cover these combinations and valid controls.

Astra's scoped source review found no remaining P0/P1 in that packet. This is
not executable qualification: no changed compiler was built, the absent type's
producer remains unproved, and the original valid Result program must still
compile and execute rather than merely receive a safer error. All authored
compiler regressions remain UNRUN under the exhausted shared diagnostic budget.

See also stage3_native_build_heap_corruption_c0000374_2026_11_08 (2026-11-08: stage3 s3_fable64b.exe heap-corrupts on hello world, blocks retest).

## 2026-11-09 — resolved-disappeared (native)
Native re-run 2026-11-09 with the current self-hosted stage2 `C:/dev/p3new/stage2new/stage2_new4.exe` (`native-build --entry-closure`, llvm, x86_64-pc-windows-gnu, core-c-bootstrap, SIMPLE_HIR_CACHE=0, clean sparse worktree of origin/release/1.0.0 @1cc167e37fd): the original fixture `test/fixtures/compiler/phase2_result_byte_codec/result_payload.spl` (unchanged) builds, links and runs: `RESULT rc=0 stdout=[PASS Result byte-array and codec payload: 3 assertions]` (build 353 s, peak 0.96 GB). The crash belonged to the old phase2 producer. Side finding: the Nov-4 Rust seed `bin/simple.exe run` exits 139 on ANY passing `assert(...)` in a plain `fn main` (JIT path) — seed is stale vs release; not this bug.

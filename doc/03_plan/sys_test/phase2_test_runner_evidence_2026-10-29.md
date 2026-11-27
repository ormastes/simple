# Phase 2 runner evidence

Status: INCOMPLETE; no release admission.

Subsequent narrowly scoped fixes landed as PR #5297 (export closure), #5298
(VmFlags), #5300 (idle MIR), and #5301 (monomorphization scope; merge
`21a165d3ce458cd5e40775d3f1d40dd99fccec05`). The idle-MIR focused regression reports PASS
in `/tmp/simple-release-1.0.0-phase2-attempt6-idle-mir-evidence-20261029/receipt.env`;
its object was not executed. In a separate VMM scoped monomorphization probe,
all three actual archive phase-4 jobs finished, followed by a downstream MIR
declaration-integrity failure and a bounded timeout (status 124, no object).
The retained receipt is
`/tmp/simple-release-1.0.0-phase2-attempt6-vmm-mono-evidence-20261029/receipt.env`.
Its finalized status is TIMEOUT, SHA-256
`c4b0e4e458a84dfc5bbb8d49ef7471cee60c5c6aa55ace178b6ec5aba58d21d0`;
no rerun occurred. A pre-scope MIR root issue is a hypothesis, not an
established cause or predicate. These focused results do not change the six
full-attempt stop or qualify the unlanded, unexecuted runner changes.

Attempt 6 reached terminal overall exit 1. The full CLI failed with status 88:
peak RSS 50,349,068 KiB exceeded the unchanged 50,331,648 KiB cap. No CLI
artifact was admitted. The test-runner build failed with status 1 at HIR
aggregation: 285 of 304 modules lowered and 19 were blocked, including
`test_result_wrapper.spl` and `test_runner_execute.spl`; no runner artifact was
produced. Compared with attempt 5's 277 lowered and 27 blocked, eight blockers
were resolved, with no newly blocked modules or crashes. Seven independent generated-module
diagnostic object builds passed; the documentation-only `app/__init__.spl`
was unsupported. These diagnostic results do not qualify the failed products.
The terminal receipt is
`/tmp/simple-release-1.0.0-phase2-combined-build-attempt6-status.env`; detailed
task and module evidence is in
`/tmp/simple-release-1.0.0-phase2-combined-build-attempt6-20261029/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`.

The six-cycle repair limit is exhausted; no seventh full attempt is authorized
by this session. The executable acceptance matrix, runtime regressions, and
broader required verification remain unexecuted against the patched CLI and
runner. The requested work and release admission remain incomplete.

Attempt 5 finished with overall exit 1. Both compiler CLI and test-runner
builds failed during HIR aggregation; neither produced a qualified artifact.
The CLI build took 787 seconds and three worker claims exited -139 on
`src/os/kernel/memory/vmm.spl`, `src/os/kernel/arch/x86_64/paging.spl`, and
`src/os/kernel/memory/vmm_address_space.spl`. A separate diagnostic module
campaign retained seven generated `_cg/*/main.spl` empty-MIR failures and an
incomplete inventory. The runner build also failed HIR aggregation; blocked
modules are not successful artifacts. Canonical task, module, and log paths:
`/tmp/simple-release-1.0.0-phase2-combined-build-attempt5-20261029/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`.
Acceptance, regressions, and broader verification remain unexecuted against
the requested patched products. Do not count failed or blocked rows as passes.

Five related fixes merged to `release/1.0.0`: PR #5283 fixes LLVM provider detection; #5285 establishes memory policy;
#5289 bounds parse-fiber reservations; #5291 reduces HIR surface path
allocations; and #5294 fixes process-capture text ABI dispatch. Other-session
fixes in reviewed ancestry include #5175, #5176, #5212, and #3895. These independent
merges do not qualify the pending runner. A subsequent reviewed idle-MIR
patch exists locally at combined head `b0c0cc77d6f`; it has not been validated
by a fresh build or landed. The finite external acceptance harness is
`/tmp/phase2_runner_acceptance.py`; it has been syntax checked and reviewed,
but has not run.

Derived CLI attempt 2 also failed with exit 88 (rss-cap-exceeded):
peak_rss_kib=50336140, cap=50331648. No CLI artifact; runner build and
acceptance harness did not run. Logs/cache remain in
/tmp/simple-phase2-runner-derived-20261029. Three workers last reported full
4469-file source loads before any HIR phase completion. Further attempts
require a concrete repair or new evidence; full CLI fix/verify attempts=2/6.

Full CLI compiler verification FAILED, attempt 1: exit 88,
status=rss-cap-exceeded, peak_rss_kib=50513800 versus cap=50331648,
compiler_jobs=8. No OOM kill. Eight worker logs show repeated 4474-file
source loads. Compiler basic admission is not full verification PASS.
Preserve the failed campaign and caches; investigate worker memory duplication
before retrying with the requested 20 cores. Do not relax the memory cap.

Phase 2 candidate linked: 1612 modules compiled, 0 failed. Canonical sanity
bootstrap_mode=0 reports result=pass, raw_status=0 for p2_add, SCV prime,
MIR retention, module path naming, and positional Hello World. Evidence:
/tmp/simple-release-1.0.0-phase2-cranelift-build/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.status.env.
Bootstrap mode 1 also reports result=pass, raw_status=0 for all five probes
in stage2-sanity.env.frontend-bootstrap-1.status.env. The canonical flow
completed struct-receiver capability proof (status=pass). Phase 2 admission v2
is status=admitted at
/tmp/simple-release-1.0.0-phase2-cranelift-build/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env.
Compiler SHA256: e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6.
This admits the compiler only; patched runner execution remains pending.

Derived patched CLI attempt: all seven parse shards exited 0. Shard 4/7
(PID 563491) was a significant straggler: observed 13207768 KiB RSS and five
minutes CPU-active before natural completion. LLDB live attach was denied by
host ptrace policy; no stack or exact responsible source file was recovered.
Track as a performance issue; do not describe it as an infinite loop.
HIR then admitted 3 workers from requested 20 using 9000000 KiB/worker and
the unchanged 50331648 KiB tree cap. Full build verdict remains pending.

Completed checks for this change:

- LLVM static provider regression: 29 checks passed (LLVM lane).
- LLVM detector fix merged independently via PR #5283 into release/1.0.0,
  commit 693bf158ba4d7a16c29c12c3aaef65a1ee5929f4. GitHub merge state verified.
  CI was pending at merge; focused regression and real-provider detection passed.
- Working diff environment/process facade guard: PASS.
- Staged environment/process facade guard: PASS (no staged implementation yet).
- Executable specs under doc/06_spec: 0.
- LLDB 18.1.3 local installation: /bin/true launched and exited 0.
- LLDB worker investigation: unauthenticated shard request rejected; genuine
  coordinator-produced one-file request replay completed HIR and exited 0.
  Collector breakpoint was bypassed, so no backtrace is claimed. Evidence:
  /tmp/simple-phase2-lldb18/admitted-worker-source-loading.log.
- Astra static routing review: identified defects repaired; execution pending.

Build process: bootstrap driver 518154, stage2 native compiler 531635,
output /tmp/simple-release-1.0.0-phase2-cranelift-build. Live observation showed
CPU progress and approximately 2 GiB compiler RSS, below the 48 GiB cap.
The Rust seed reports dynload unsupported and emits one-binary; no dynload
qualification is claimed. This seed is used for bootstrap only.

Pending: full compiler verification, patched CLI build, positive/negative/empty acceptance
matrix, enabled verbose log validation,
broader required verification, refreshed target review, and merged PR.

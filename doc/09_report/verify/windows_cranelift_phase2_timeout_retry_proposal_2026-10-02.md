# Cranelift retry proposal: 80 workers and a 1,200-second file timeout

**Proposal only; not launched.** Fresh user authorization is required because the prior additional Cranelift attempt was consumed and the session repair cap remains in force. The separate LLVM attempt must finish before this retry starts, preserving the user's requested backend sequence.

The exact prepared command is `bash C:/Users/user/.simple/runtime/propose-cranelift80-timeout1200-retry.sh --authorized-retry`. The script passed syntax validation. No retry, build, or test was launched.

## Proposed inputs and bounds

Use frozen source `C:/dev/simple-windows-phase2` at commit `1ffaf797bab1b6747d4e24856ed6c1af990e178e`, the validated receipt `evidence/cranelift-resume/windows-materialized-links.1ffaf797.env`, and the evidenced MSVC LLVM 23.1.1 toolchain. Reuse the existing private `build/bootstrap-cranelift80` output. Retain 80 build workers, 80 test workers, and `SIMPLE_NO_STUB_FALLBACK=1`. Set `SIMPLE_NATIVE_FILE_TIMEOUT=1200`, with an independent 7,200-second Windows Job Object guard and a 128 MiB log limit. Each attempt gets unique logs; failed attempt 4 remains intact.

## Cache cohort analysis

The [failed attempt](windows_cranelift_phase2_80_worker_timeout_2026-10-02.md) reported 995 compiled objects, no reuse, and 123 failures. Its current `.bootstrap-cache-binding` records `phase=stage2`, `entry=bootstrap-main`, producer SHA-256 `90e2a8ddaa1915b384bae2c1c7da1cd4c67e3bfde5d271aa72e5cdb246ec68c3`, and inputs SHA-256 `73c93cf02af45374c91394ab79504af630e39abce3ff68315f9a7813641c3e56`. The inner scope is `scope-37e51c496ff7919b`.

Source inspection shows that the outer Stage2 cache context binds source, runtime, tool snapshots, release options, and frontend/HIR persistence policy. The Stage2 release options omit the per-file timeout. The bootstrap-only Rust cache scope binds producer bytes and lane; its object key binds source content, entry, backend, mangling, prefix, optimization level, CPU/SIMD settings, producer, and lane. The timeout is absent from both. A timeout-only change from 300 to 1,200 seconds should therefore preserve the existing cohort if source root and all producer/source/runtime/tool bytes remain identical.

The Stage2 invocation's argument SHA does include `--timeout`. The canonical wrapper must produce a new transcript; existing binding stamps and admission receipts must not be rewritten or reused as new evidence. No cache hit can be claimed until a real build reports reuse and rebuild counts. A cache-owner refusal must be reported, never bypassed. A changed Rust producer or shared tool identity can legitimately prevent reuse; preserve the existing objects regardless.

## Required outcome

The authorized incremental attempt must report actual cache reuse, produce the Phase2 compiler, and pass strict sanity, admission, and current invocation lineage. It must then build and execute the full CLI, test runner, and native interpreter, loader, compiler-core, HIR, and MIR executables, with positive test counts and complete inventories. Known explicit-entry collector exclusions may still block qualification; those require a reviewed pure-Simple repair and cannot be represented as a passing test result.

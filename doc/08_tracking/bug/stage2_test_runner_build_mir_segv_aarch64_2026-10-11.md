# Stage-2 compiler SIGSEGV in provider-relocation chain during test_runner native-build (aarch64 Linux, 2026-10-11)

- **Filed:** 2026-10-11 (beta-release qualification lane)
- **Status:** OPEN (P0 — blocks the strict bootstrap Stage-2 compiler-test matrix
  and therefore the Stage 3→4 receipt chain on aarch64 Linux)
- **Host:** aarch64-linux (20-core, 121 GB), backend=cranelift, mode one-binary,
  `--runtime-bundle core-c-bootstrap`, stage-2-admitted compiler
- **Root-cause class:** stage-native codegen miscompile (the "stage-native lane
  loses the declared value type at indexed/nested struct access" family, same as
  module_build #2693 / 7370e13e86d). NOT a logic bug in provider relocation.

## Symptom

`bootstrap-phase-verification --phase=stage2` task `test_runner_build` (and the
same command standalone) dies:

```
error: native-build worker terminated with signal 11 before producing a binary; NOT a compile failure.
  A SIGSEGV/SIGABRT is a crash in the compiler itself; take a backtrace from the core (see /var/crash).
```

Reproduced 4/4 times on 2026-10-10/11 (two in-lane matrix runs, one standalone
`run-linux-phase2-tests.shs`, one direct run). Watchdog receipts show
`status=complete exit_status=139` with peak RSS well under the cap (4.8 GB vs
6.8 GB) — a genuine memory-safety crash, not a resource kill.

## Confirmed backtrace (apport core, 2026-10-11)

```
#0 MirLowering.relocate_provider_type          (provider_metadata.spl)
#1 MirLowering.relocate_provider_default
#2 MirLowering.register_provider_class
#3 MirLowering.lower_module
#4 lower_module_transient_scoped
#5 CompilerDriver.lower_to_mir{,_with_target_context}
```

Faulting instruction (stage2-admitted binary, PC 0xc7ac70):
`ldr x20, [x26]` with **x26 = 0**, fault address **0x0**. Register chain:
x19 = 3 — i.e. an enum discriminant word (2) OR'd with the heap-tag bit (|1)
and then masked (& ~7 = 0) by the tagged-value autodetect copy loop: a small
integer was read where a boxed 48-byte `HirType` pointer belonged, tagged, and
dereferenced. `HirExpr` is `{kind, has_type_: bool, type_: HirType}` and
`HirType` is `{kind: HirTypeKind, span}` — reading `type_` at a wrong offset
yields the kind discriminant word exactly like this.

## Minimal reproduction

```
env SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  SIMPLE_RUNTIME_PATH=<phase2-runtime-capsule dir> \
  <stage2-admitted>/simple native-build src/app/test_runner_new/main.spl \
  --backend=cranelift --low-memory --threads 2 -o /tmp/simple_test_runner
```

from the repo root (~6 min to crash under host load). Cores: enable
`unpackaged=true` in ~/.config/apport/settings, then `apport-unpack
/var/crash/<report>.crash` and gdb the CoreDump (the in-process SIGSEGV handler
intercepts before an attached gdb on the parent sees anything; the crash is in
the spawned `native_build_worker` child).

## What was already tried (do not repeat blindly)

1. 2026-10-08/09 (commits 79a2e5d1994, 951fc8ad74b, 9ff81f2a22a, dc8d726c323,
   7370e13e86d, all ON MAIN): has() probes before get_symbol_raw, explicit
   `val kind: HirTypeKind = type_.kind` / `val expr_kind: HirExprKind =
   expr.kind` annotations, HirField/typed-local transports. These cleared the
   10-08/09 crash sites; the 10-11 core shows a residual instance one level
   up the same chain.
2. 2026-10-11 (this lane, commit a880d960302, REVERTED unmerged): extended the
   same annotation idiom to relocate_provider_types / relocate_provider_args
   (for-loop vars -> indexed typed locals) and `expr.type_`. Semantically
   identical rewrite. Result: the SIGSEGV moved — the rebuilt compiler instead
   fails in the HIR-shard worker on src/compiler/10.frontend/core/cfg_platform.spl
   with `[simple-runtime][error] rejected invalid array handle before
   dereference; probable compiler/FFI ABI mismatch` (4 occurrences,
   deterministic across fresh caches, 0 occurrences with the unpatched
   compiler). Conclusion: source-level annotations re-arrange which function
   the backend miscompiles; they do not remove the defect.

## Evidence

- /tmp/beta-qual-evidence/crash-u/ (unpacked apport core: CoreDump, ProcCmdline)
- /tmp/beta-qual-evidence/segv-repro{,2,3,4}.log, repro-after{,2}.log
- /var/crash/ 2026-10-03 `compiler.snapshot ... stage2-compiler-tests ...
  .crash` files from an earlier session — same failure family predates this lane.

## Required real fix (follow-up lane — compiler backend)

The defect is in the stage-native (cranelift dynload) MIR lowering of
struct/array value copies: somewhere in this call chain a value's declared type
is lost and an enum discriminant word is materialized where a boxed value
pointer belongs. Find the actual miscompiled function/instruction pattern in
the backend (compare LLVM-backend output for the same function as ground
truth), fix the lowering once there, then remove the source-level annotation
workarounds accumulated in provider_metadata.spl (7370e13e86d et al.) as
follow-up cleanups. Until then, the strict-bootstrap test matrix stays red on
aarch64 cranelift.

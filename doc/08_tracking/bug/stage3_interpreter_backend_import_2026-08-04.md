# Stage 3 interpreter Backend import failure

## Status

Pure-Simple ownership repair implemented and the original `Backend` diagnostic
did not recur in fresh cycles 1, 2, or 3. The full-bootstrap lane remains open:
final-cap cycle 3 ended in host memory/resource termination at one job. Stage 4
and QEMU remain separate, unverified gates.

## Exact failure

Cycle 3 built and sanity-checked Stage 2, parsed all 543 Stage 3 closure files,
completed HIR/type checking, and passed the former `VhdlProcessKind`, `Symbol`,
and `Token` failures. Monomorphization then failed normally:

```text
phase3:hir_typecheck:done
phase4:monomorphize:start
[ERROR] phase 4 FAILED
error: in-process native-build: HIR lowering error in
src/compiler/backend/backend/interpreter.spl: unresolved type: Backend
```

Retained evidence:

- `build/bootstrap-clang-23-1-stage4-token-owner-cycle3.out`;
- `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`;
- `build/bootstrap/bootstrap-progress.log` (`exit-1`).

## Ownership repair

`compiler.backend.backend.interpreter` materializes `EvalContext` from
`backend/env.spl`. That context retained an unread `backend: Backend` field,
while the same module retained an exported but unused `HirVisitor` against the
same nonexistent legacy interface. `backend_api.Backend` is not that interface;
it aliases `CompilerBackend`, so importing it would mis-type the
`InterpreterBackendImpl` value passed by the caller.

The pure-Simple repair removes the unread context field, its constructor
arguments, and the zero-consumer visitor/export. It preserves the separately
tracked work to design a real shared backend trait rather than binding this
closure to an unrelated alias. Exact source-boundary and adjacent JIT/context
constructor regressions accompany the change.

## Bounded verification evidence

Fresh cycle 1 used the no-stub full-bootstrap path with Cranelift and the full
CLI closure. It admitted Stage 2, parsed all 543 Stage 3 sources, and completed
HIR for both `backend/interpreter.spl` and `backend/env.spl`; the former phase-4
`unresolved type: Backend` diagnostic did not recur. The run later terminated
with host SIGKILL/exit 137 while importing `backend_port.spl`, without a new
compiler diagnostic.

Retained cycle-1 log:

- `build/bootstrap-clang-23-1-stage4-backend-owner-cycle1.out`.

Cycle 2 preserved the caches and lowered concurrency to `--jobs=2`. It admitted
Stage 2, parsed all 543 Stage 3 sources, and cleared the former unresolved
`Backend` failure. Phase 4 then failed normally in `backend/codegen.spl`: its
broad `use compiler.mir.*` made HIR's `Effect` struct conflict with MIR's
`Effect` enum. Its retained evidence is:

- `build/bootstrap-clang-23-1-stage4-backend-owner-cycle2.out`.

The adjacent owner repair replaces the broad MIR wildcard with selective
imports of `mir_types`, `mir_instruction_support`, and
`mir_instruction_graph`, and removes the unused HIR `SymbolId` import. This
keeps the two legitimate `Effect` owners distinct.

Final-cap cycle 3 preserved the caches and used `--jobs=min` (one job). Stage 3
completed HIR for `backend/codegen.spl` (38 functions), proving neither the
former `Backend` error nor the cycle-2 `Effect` conflict recurred. It advanced
through `backend/compiler.spl` into `backend/sdn.spl`, then the host terminated
it with SIGKILL/rc 137. No compiler diagnostic replaced the cleared owner
failures. Its retained evidence is:

- `build/bootstrap-clang-23-1-stage4-backend-owner-cycle3.out`;
- `build/bootstrap/bootstrap-progress-cycle3.log`.

The three-cycle cap is reached with Stage 3 memory/resource termination even at
one job. No Stage 3 or Stage 4 candidate is claimed. A Stage 4 provenance
receipt, the exact essential-tools smoke, and the LLVM-default SimpleOS WM QEMU
evidence do not exist; QEMU was not run after the cap. Resume in a fresh scoped
session from the preserved bootstrap caches and the cycle-3 logs.

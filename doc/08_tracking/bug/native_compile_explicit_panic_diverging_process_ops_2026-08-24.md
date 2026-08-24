# `native-build` of an `io_runtime` importer fails with `explicit panic() -- diverging, must not fall through`

**Status:** Open — SIXTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 35.semantics (divergence / fall-through analysis), `std.nogc_sync_mut.io.process_ops`
**Predecessor:** `native_compile_nonterminating_io_runtime_2026-08-24.md`
(blocker #5, RESOLVED — the exponential `ssa_block_can_reach` DFS)

## Position in the chain

Blockers 1-5 are fixed. With blocker #5's hang removed, `native-build` of an
`io_runtime` importer now **terminates** (181 s) instead of spinning past
3600 s — and fails with a real, reported diagnostic.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`).
Exit codes read DIRECTLY into a variable on the line after the command, never
through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 600 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1     elapsed=181s
```

```text
error: explicit panic() -- diverging, must not fall through
error: semantic: panic: compile error: explicit panic() -- diverging, must not fall through
```

Five occurrences of `explicit panic()` in the full stderr.

## Context reported alongside (may or may not be causally related)

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops dependency=Option: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Option` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops dependency=Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Option / Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Option / Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.signal_stubs dependency=fn: ...
```

Also reported, and worth checking independently:

```text
warning: public function `env_get` has 3 co-compiled definitions with 2 differing
signatures ((text)->Optional(text) vs (text)->text); JIT call sites resolve by exact
arg-type match ... a fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

`env_get` is precisely the function the reproduction calls, and the control
program's `use` is what pulls in all three definitions.

## Not yet measured

- Which `panic()` site, in which function, raises the diagnostic. The message
  carries no file/line — that is itself a defect worth fixing first, since it
  makes the error nearly unactionable.
- Whether the unresolved `Option`/`Result` dependency origins above are the
  cause (a `panic()` in a branch whose type is unresolved may be
  mis-analysed as falling through) or independent pre-existing noise.
- Whether the `env_get` signature collision is implicated.

## Note on stderr truncation

The worker's stderr is middle-dropped (`16470 of 28470 bytes ... dropped from
the MIDDLE`). The full stream is saved to a named file
(`[native-build] FULL stderr (28470 bytes) saved to: ...`) — read that file
rather than counting over the truncated console output, which the tool itself
labels unreliable.

## Gate

Not yet fenced. Blocker #5's gate
(`scripts/check/check-ssa-block-reach-not-exponential.shs`) deliberately
asserts NON-HANG and NAMES this residual exit 1 rather than asserting exit 0;
its `--require-success` flag turns exit 0 into a hard assertion and should be
switched on as the default once this bug lands. The same applies to
`--require-success` in
`scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`, which is
deliberately still NOT the default for the same reason.

## Operational note

`timeout` kills the `native-build` parent but the `native_build_worker.spl`
child can survive as a multi-GB, 100%-CPU orphan. Check
`pgrep -af native_build_worker.spl` after any interrupted reproduction, and kill
only the PIDs belonging to your own working directory — other lanes run their
own workers.

---

## RESOLVED 2026-08-24 — root cause, fix, and measured evidence

**Status:** FIXED. The `explicit panic()` signature is gone from the repro
(5 occurrences -> **0**, measured on a freshly rebuilt seed). `native-build`
still exits 1, but on a **different, independent** failure now filed as
blocker #7 — see "Residual" below. `--require-success` is therefore
deliberately **NOT** flipped on the staged gates.

### Root cause

The message was never a diagnostic. It is the **reason label** of a
`MirTerminator.Abort`, written by `terminate_abort(...)` at
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1651` — the
lowering of every user `panic()`. That is why it carried no file/line: there
was no span to carry.

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` lowered
`case Abort(message)` by calling `emit_unsupported_panic(message)`. That was
harmless while the helper merely emitted `@rt_panic` + `unreachable` IR —
which is exactly the correct lowering for a diverging Abort block.

On **2026-08-23**, `emit_unsupported_panic` was converted from "emit the IR"
into "**FAIL THE BUILD**" (`llvm_backend_unlowered_mir_kind_fails_open`,
closing a genuine fail-open where an unlowerable MIR kind linked green and
died at runtime). That change was right for its ~100 genuine
"backend does not support X" call sites, and **collateral damage** for the one
call site that was not an unsupported kind at all: `Abort` is a fully
SUPPORTED terminator, deliberately emitted.

Consequence: every user `panic()` in any co-compiled module became a hard
compile error, and its abort reason label was printed as `error: ...`. The
five occurrences were five `panic()` sites in the transitively compiled
stdlib, not five distinct defects.

**Decisive control — the same construct in sibling backends:**

| backend | `case Abort(message)` lowering | correct? |
|---|---|---|
| LLVM (`_MirToLlvm/core_codegen.spl`) | `emit_unsupported_panic(message)` | **NO — the defect** |
| C (`_CBackendTranslate/instruction_lowering.spl:664`) | `spl_panic("...")` directly | yes |
| cranelift (`cranelift_codegen_adapter.spl:922`) | `cranelift_trap(ctx, 1)` | yes |

LLVM was the **sole** offender. Two backends lowering the identical
terminator to a trap is what rules out "Abort is genuinely unsupported".

### Fix (minimal, semantics-preserving)

The ~7 lines of trap IR at the bottom of `emit_unsupported_panic` were
extracted into `me emit_panic_trap_ir(message)`
(`_MirToLlvm/asm_constraints_helpers.spl`). The `Abort` arm now calls that
directly; `emit_unsupported_panic` calls it on its allow-path.
**`emit_unsupported_panic`'s error semantics are untouched** — the ~100
genuine unsupported-feature sites still fail the build, so the 2026-08-23
fail-open stays closed.

### Leads from the previous lane — outcomes

1. *"The error carries no file/line — fix the diagnostic first."* Correct
   instinct, and the absence was itself the clue: an Abort reason label has no
   span because it is not a diagnostic. Reading the emission site was enough;
   no instrumented probe was needed.
2. *"`env_get` has 3 co-compiled definitions with 2 differing signatures."*
   **Not implicated.** Pre-existing noise. The mechanism above explains the
   error, the missing file/line, and the debug-flag heisenbug without it. The
   warning remains open on its own merits.
3. *`SIMPLE_BOOTSTRAP_DEBUG=1` is a heisenbug.* Confirmed and consistent: that
   arm never calls `llvm_bootstrap_ssa_function`, so it never reaches this
   Abort lowering. Equally, **`SIMPLE_ALLOW_UNLOWERED_MIR=1` must not be used
   to verify this fix** — it greens the run through the helper's escape hatch
   without exercising the Abort arm at all. Neither flag was used.

### Measured evidence (fresh seed, exit code read directly into a variable)

```text
$ timeout 900 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1
$ grep -c 'explicit panic() -- diverging' nb.err
0            # was 5 before the fix
```

### Residual — blocker #7, NOT this bug

`native-build` now fails with:

```text
error: build failed: 3 failed, 0 unverified, 0 not run, 3 ok of 6 unit(s)
  ERROR: std.nogc_sync_mut.io.file_ops, std.nogc_sync_mut.io.process_ops,
         std.nogc_sync_mut.io_runtime
```

The three ERROR modules are **exactly** the three owners of the
`[hir-callable-dep-origin-unresolved] dependency=Option / Result` reports this
record listed under "Context reported alongside". That answers this record's
own open question: those reports were **independent**, not a consequence of
the panic defect, and they are now the blocking failure. Filed as
`doc/08_tracking/bug/native_compile_unresolved_option_result_io_modules_2026-08-24.md`.

### Gate

`scripts/check/check-llvm-abort-terminator-not-unsupported.shs` —
`--selftest` first and fatal (7 fixtures), verdict last, PASS/FAIL/ERROR with
exit 0/1/2, `--build` runs a real `native-build` under `timeout` with
**rc=124 classified as a distinct HANG** failure. Mutation-tested both
directions: reverting the Abort arm to the helper must FAIL, and reopening
the 2026-08-23 fail-open must also FAIL.

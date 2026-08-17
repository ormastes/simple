# Stage 4 HIR Import Crash

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

PARTIALLY FIXED. The native `Dict.get()` crash is fixed by using
`contains_key` plus index reads for struct-valued module entries. A fresh
strict bootstrap now passes Stages 2 and 3 and lowers all Stage-4 modules
without a segfault, but the full CLI remains blocked by deterministic import
resolution errors.

## Evidence

The focused Stage 4 run parsed
`src/compiler/mir/_MirLoweringExpr/expr_dispatch.spl` successfully, entered HIR
lowering, and stopped at:

```text
phase3:hir:file:start src/std/nogc_sync_mut/io/env_ops.spl
resolve_import_symbols:start module=src/std/nogc_sync_mut/io/env_ops.spl
```

Kernel evidence reports a null dereference at `0x5031f2`. `addr2line` and
disassembly map that address to `HirLowering.lower_trait`, where the generated
code dereferences its `Trait` argument. The leading hypothesis is the
`register_imported_symbol` path: its generated code calls `rt_enum_payload`
for `as_trait.unwrap()` immediately before calling `lower_trait`. No retained
core/backtrace proves that this caller supplied the null argument.

- Stage 2 SHA-256:
  `51c072812d5cd4b5b80ca2ff289d4e13d3a830adf679e58d61da6762066f816f`
- Stage 3 SHA-256:
  `c2a638a51df632e27352543a458289e857c16bfefd79e020bcce39c608f6870a`
- Strict run peak RSS: 2,549,240 KiB
- Focused Stage 4 peak RSS: 2,976,672 KiB
- Focused log:
  `build/bootstrap/cosmos-production-20260727/stage4-focused.log`

The unchanged-tree strict follow-up passed Stage 2/3 sanity and entered Stage
4. It no longer crashed in `HirLowering.lower_trait`; it reported unresolved
names beginning with `cli_run_file` in
`app.cli._CliMain.args_and_os_commands`, followed by other symbols supplied
through partial/header-only import facades.

- Follow-up Stage 2 SHA-256:
  `00fcb65729acfe1f7bd30e113d7d96bea4cd7ff2e4f596667cda8c6a97c89411`
- Follow-up Stage 3 SHA-256:
  `772f9a2e6d104500c5cd1c661c15b6e0083fd9c936787803bb05f5ad824c17b3`
- Follow-up peak RSS: 5,492,252 KiB
- Follow-up elapsed time: 45:32.18
- Follow-up log:
  `build/bootstrap/cosmos-production-20260727-current/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

An additional focused reproducer on 2026-07-27 was:

```text
release/x86_64-unknown-linux-gnu/simple check src/lib/common/ui/host_env_contract.spl src/app/test/test_host_env.spl
Checking src/lib/common/ui/host_env_contract.spl...
exit 139
```

It was not retried; shell/static validation covered the pending host-evidence
change instead. An earlier strict-wrapper attempt did not reach Stage 4 because
a tracked documentation edit changed the dirty-state fingerprint during
provenance measurement; Stage 2 and Stage 3 had already passed sanity.

The same release executable also dumped core with exit 139 before reporting a
scenario for:

```text
timeout 60 release/x86_64-unknown-linux-gnu/simple test --no-session-daemon test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl --mode=interpreter --clean
```

That command was also not retried.

## 2026-07-27 Fresh Bootstrap Result

The isolated strict command ran once:

```text
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --mode=one-binary \
  --output=build/bootstrap/codex-perf-stage4 --jobs=half --no-mcp
```

Stages 2 and 3 passed. Stage 4 exited 1 with 6,144 HIR lowering errors,
starting with unresolved facade-imported CLI symbols and ending with unresolved
types and untyped-return diagnostics. The retained log is
`build/bootstrap/codex-perf-stage4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`.
No retry was made.

The installed `release/x86_64-unknown-linux-gnu/simple` is independently stale:
its linked `rt_env_set` has the obsolete two-argument raw-C-string ABI while
current generated callers pass pointer/length pairs. GDB observed libc
`strlen` dereferencing `0x1b`. Current runtime source already has the four-
argument ABI, so the stale executable must not be used as verification evidence.

## Required Fix

Finish canonical facade re-export, transitive-star, receiver-keyword, and
numbered/unnumbered module-key resolution without restoring opaque-symbol
fallbacks. Preserve cross-module default-method lowering from issue #190.
Then run one strict bootstrap from an unchanged tracked tree and replace the
stale deployed executable only after the Stage-4 admission gates pass.

## 2026-07-27 Final Bounded Attempt

Small read-only classifier lanes separated the 6,144 diagnostics into facade
exports, receiver aliases, unknown generic return types, duplicate physical
module aliases, and residual import defects. The shared fixes added explicit
facade exports, made `me` fall back to the synthesized `self` receiver, kept an
unknown written generic return typed as `Any`, and lowered each physical entry
source once while retaining its logical module aliases. A focused native probe
covering all three behaviors compiled and printed `42`.

The canonical final command used
`build/bootstrap/codex-perf-stage4-final`. Stages 2 and 3 passed sanity. Stage
4 no longer failed in closure loading, but exited 1 with 1,701 HIR diagnostics
(646 unique messages): 1,576 unresolved names, 107 untyped returns, 10
unresolved types, and 7 generic diagnostics. The largest remaining groups are
`TokenKind` (185), `HirTypeKind` (96), `Expr`/`ExprKind` (40 each), and the
T32 easy-fix types (36-38 each). The retained log is
`build/bootstrap/codex-perf-stage4-final/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`.
This was the third verify/fix cycle, so no further retry was made.

## Post-cap Source Fixes

Five small read-only lanes traced the largest residual clusters without another
bootstrap. Source fixes now use explicit owner or named-facade imports for the
TreeSitter `TokenKind` surface, HIR types, flat-AST expression accessors,
legacy MIR optimizer passes, T32's `AccessResult` compatibility name, EasyFix,
and C-backend HIR fields. This avoids globally treating private glob imports as
re-exports, which the current parser cannot distinguish from `export use`.

A strict focused entry-closure probe compiled 142 modules with
`SIMPLE_NO_STUB_FALLBACK=1`, linked with one resolved `char_from_code`
compatibility alias, and printed `42`. This proves the repaired import surfaces
can lower and link in that closure; it does not replace full Stage-4 admission.
The retained unannotated value-returning diagnostics are tracked as TODO590;
their physical-source count is corrected below. No fourth bootstrap was run.

## Bounded Return-Contract Slice

Parallel owner review corrected the inventory to 97 physical declarations;
hardlink/module aliases inflated the 107 retained emissions. Twenty-seven
body-proven declarations now have explicit returns. Strict no-stub native probes
print `42` for AOP/color, VHDL metadata/call lowering, and `array_chunk`. The broader generic
array probe crashed, so its other annotations were reverted. The fixed-Huffman
gzip probe linked without stubs but compressed 11 bytes to 31 and decoded zero;
an explicit `gzip_header_size -> i64` did not change that behavior, and TODO591
owns the remaining diagnosis after three cycles. The platform facade's direct
named re-exports remove its undeclared `path` global: strict four- and 362-module
closures link and print `42`. TODO592 now tracks the generic compiler-level
namespace-call lowering proof. Full Stage 4 was not rerun.

## Generic Namespace-Call Root

A minimal two-module strict native probe (`use .provider` followed by
`provider.answer()`) reproduces the remaining compiler symptom exactly:
LLVM receives a `LoadGlobal` for the compile-time-only alias `provider`.
HIR field lowering scanned `SymbolTable.symbols.values()`, but native reads of
struct-valued dictionary values are corrupt on this lane. It now uses the
already-proven `keys()` plus bracket-index pattern and returns an HIR error when
a module member cannot resolve instead of falling through as a runtime field.

The HIR regression includes a same-named local `answer`, and the new strict
two-file system SSpec requires the provider result `42`, no undeclared symbol,
and no generated fallback stub. A focused current-source closure compiled all
117 required modules but could not link against the limited retained
core-C-bootstrap ABI (`Dict.has`, `rt_is_debug_mode_enabled`,
`rt_array_extend_i64`, and `rt_option_map` are absent). That is not execution
proof; TODO592 remains open for the fresh admitted self-hosted runner. No full
Stage 4 was rerun.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STALE-REF

The cited `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` no longer
contains the diagnostic text: `grep -rn "unresolved import" src/compiler/20.hir/`
returns zero hits across the whole 20.hir layer. Location must be re-established
before this row can be actioned. Owner path: src/compiler/20.hir/hir_lowering/**.

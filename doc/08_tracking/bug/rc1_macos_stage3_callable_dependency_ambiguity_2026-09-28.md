# RC1 macOS Stage 3 callable dependency ambiguity

**Status:** Fix under admission. **Platform:** `aarch64-apple-darwin`.

On RC1 commit `482266d0871`, the full Stage 2 compiler passed sanity and was
admitted. The canonical Stage 3 resume created its memory snapshot with the
required `run_id` and 25 fields, passing the earlier snapshot-open failure.
HIR then reported thousands of `ambiguous explicit callable dependency`
errors. The first was `AsmTargetSpec` in `compiler.hir.hir_definitions` while
lowering `src/compiler/driver/driver.spl`; other early errors named `Span`,
`CompilerDriver`, and `Closure`. The build was stopped after source 57/717 as
the failing process passed 7 GB RSS on a 24 GB host.

The RC1 dependency sweep considered explicit named imports and wildcard
routes at the same rank. It also compared re-export facade indices before
canonicalizing them to the terminal declaration. The existing imports in
`hir_definitions.spl` include a named `AsmTargetSpec` alongside a wildcard
route, exposing this mismatch. `main` already contains the focused resolution
in `ffcd929a5e8`; the RC1 branch backports canonical candidate resolution and
named-over-glob precedence, with a direct sweep regression fixture.

Next gate: rebuild and admit Stage 2 on the fixed commit, then resume Stage 3
from its path-bound receipt. The fix is not admitted by this report alone.

## Second Stage 3 boundary

The resolver-only backport passed Stage 2 admission. Stage 3 no longer failed
on the initial `AsmTargetSpec` and `Span` imports, but its first remaining
fatal was `HirModule` in `compiler.backend.backend.env` at source 10/717.
`main`'s same fix includes explicit import-origin rows in that module and ten
other frontend, HIR, and backend owners. Those small source declarations are
backported with the resolver. A third source-matched admission run is required;
the second Stage 3 run was stopped while collecting the new first error.

## Third admission boundary

Commit `445b8117ab5` passed full Stage 2 trust-root admission, including the
positional frontend smoke and receiver check. Its canonical Stage 3 resume
stopped before HIR with `MC/DC global byte budget must be at least the owner
byte budget`. The Stage 3 log contains only that error; the shell environment
and command transcript contain no MC/DC budget override. The source defaults
are 1 MiB owner and 64 MiB global in `compiler/common/config.spl`. The HIR
import-origin backport therefore has not yet received a Stage 3 verdict on
this final commit. The three-cycle verify/fix cap is exhausted for this
session. Next diagnosis should inspect `CompileOptions` transfer and
`CompilerConfig.from_env()` under this exact admitted Stage 2 binary.

## Fourth admission boundary: compiled MC/DC default transport

A fresh, separately admitted Stage 2 binary reproduced the budget failure on
a small in-process native-build command with no `SIMPLE_MCDC_*` environment
variables. An instrumented error reported `owner=37526561537, global=0`,
instead of the source defaults of 1048576 and 67108864. Setting both budgets
explicitly in the environment let the same binary reach source loading. This
isolates the failure to the compiled default configuration path, not the Stage
3 source graph or a shell override.

`CompilerConfig.from_env()` now writes the two scalar defaults in its own
frame immediately after receiving `CompilerConfig.default()`, before applying
environment values; CLI overrides still follow in `CompileContext.create()`.
The diagnostic Stage 2 binary passed admission and crossed the MC/DC gate
without overrides. Its tiny hello-world native-build later exited 139 after
HIR, which is a separate downstream failure and not a Stage 3 verdict.

Canonical Stage 3 requires a planner admission bound to a Stage 2 artifact
under `build/bootstrap`; the producer correctly rejected the isolated
`build/bootstrap-mcdc-diag` tree. The fix needs canonical Stage 2 admission,
planner receipt, and Stage 3 resume before Mac bootstrap can be called green.

## Canonical cold Stage 2 boundary

The committed scalar-default fix passed the isolated diagnostic Stage 2
admission. Rebuilding it under canonical `build/bootstrap` produced a Stage 2
binary, but sanity rejected it: the positional two-line hello-world smoke
timed out at `native_compile 0/1`. The first canonical attempt used an older
incremental object cache. Eleven object names shared with the isolated cache
had different contents, so that cache was preserved under a quarantine name
and the canonical Stage 2 build was repeated from an empty scope.

The fresh canonical build reported `770 compiled, 0 cached, 0 failed` and
still timed out at the same `native_compile 0/1` smoke point. This rules out
reuse of the quarantined objects as the sole cause. The rejected cold binary
hash was `1a5b99ed8171e848e98e5b03c8ec7c401d78e7607db5258902de702b467029bc`;
the isolated admitted binary hash was
`be68e408350e30d63dd7ed62a03db6b92577450f681351ef4d04fbc6bbef6206`.
The source was the same committed fix, but the build paths and cache histories
differed. A path-dependent or cold-versus-warm native codegen defect remains
possible; the available evidence does not identify which one. The third
verify/fix cycle for this boundary is complete, so no further bootstrap retry
was started in this session. Stage 3 and the Mac release gates remain unpassed.

## Targeted cold-binary diagnosis

A fresh scoped session reproduced the canonical rejected binary's positional
hello-world hang without rerunning the full bootstrap. A five-second sample
captured 3503 main-thread samples in
`lower_mir_storage_project_fields_v1`, mostly under `rt_range` and
`rt_array_push_grow`; the process reached about 3.4 GB RSS before it was
stopped. The rejected and isolated admitted binaries have identical
instructions for this function, so the differing admission outcomes do not
come from a different copy of that function. Disassembly found exactly one
`rt_range` call in it. The storage recipe helper still had one `for` over
`binding.fields` that could inline into this owner. That remaining traversal
is now indexed `while` code, matching the prior fix for the other traversals.
The existing native projection unit spec covers selection of every field and
missing-binding behavior. A source-matched Stage 2 admission is required to
test whether this removes the cold-binary hang; no success is claimed here.

## Stage 3 after the remaining field scan was bounded

Commit `84d0a188004` passed canonical Stage 2 trust-root admission, including
the positional frontend smoke and receiver check. Its planner receipt was
produced from that admitted binary. Stage 3 then stopped before source loading
with `MC/DC global byte budget must be at least the owner byte budget
(owner=33533980673, global=0)`. This proves the earlier scalar reset inside
`CompilerConfig.from_env()` was insufficient: a later aggregate return into
`CompileContext.create()` can still corrupt the budget fields.

The next source change resolves owner and global budgets through scalar
functions in the config owner, and applies those values in
`CompileContext.create()` after receiving the aggregate. The same functions
retain the existing environment parsing and validation semantics, and CLI
overrides still apply last. It requires a new source-matched Stage 2 admission
and Stage 3 run; neither is claimed by this note.

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

## Source-matched Stage 3 HIR verdict

Commit `b50885e1a99` passed canonical Stage 2 admission and received a new
planner admission bound to that binary. Stage 3 crossed MC/DC validation,
fingerprinted and parsed its source closure, and reached HIR without the old
early `AsmTargetSpec`/`HirModule` ambiguity. It then collected 1797 HIR errors
across 117 poisoned modules in a 717-source build. The emitted error rows included
1685 unresolved names, 109 unresolved types, and two unsupported generic
method errors. There were 182 distinct unresolved symbol spellings; leading
counts included `mir_operand_copy` (483), `MirInstKind` (256),
`module_add_decl` (58), `expr_ident` (39), `ByteOrder` (38), and `Effect` (37).

The first failures include `env_get_opt` from the explicit re-export in
`std.io_runtime`, `char_code` from `std.string_core`'s export surface, and
`MirInstKind` from `compiler.mir.mir_data`. Their source declarations exist.
This suggests a common HIR import-origin/materialization gap rather than 182
missing implementations; it remains an inference until a targeted resolver
test and source-matched Stage 3 run prove it. Current `main` has later frozen
import and module-alias work, so the next investigation should compare those
resolver contracts with this RC1 lane before selecting a backport. The
three-cycle verify/fix cap is reached for this session. Stage 3 and Mac release
remain unadmitted.

## Indexed origin owner fallback

RC1's `find_reexport_source_walk` returned a miss as soon as an indexed export
origin named a module absent from the frozen surface registry. This skipped the
facade's independent frozen import and export routes. The resolver now marks
that origin miss invalid for negative memoization and continues through those
routes. A focused `reexport_physical_cache_spec.spl` case supplies a missing
indexed owner and a valid imported declaration, and checks that the declaration
is found while the walk remains invalid for negative caching.

At the time of this note, the fix had not passed a source-matched Stage 2/3
bootstrap. The admitted
Stage 2 compiler does not expose `test`; the older installed release test
runner cannot parse the current `module_surface_types.spl`, so the new case is
not yet executable in this lane. Another macOS Stage 2 run was active in a
separate worktree when this fix was prepared, so no competing bootstrap was
started. The 1797-error Stage 3 log predates this change and is not evidence
that the fix clears those errors.

## Source-matched verdict and residual Stage 2 spread defect

A first Stage 2 build with the indexed-origin fallback compiled three objects
and reused 767, but its positional hello-world sanity timed out at
`native_compile 0/1`. A five-second standalone probe of the rejected binary
sampled 2,060 frames in `lower_mir_storage_project_fields_v1`, including 1,926
in `rt_range`; the current source had no explicit `for` loops in that function.
Its remaining `MirFunction(..function, blocks: blocks)` spread emitted an
`rt_range` call with a tagged aggregate value as its end bound. Replacing the
spread with a mutable local function and `function.blocks = blocks` removed the
`rt_range` relocation from the rebuilt function object. The second source-
matched Stage 2 build passed full trust-root admission, including positional
sanity and receiver proof. Its admitted candidate SHA-256 was
`cc73ebabcc846a45aa3ec20817ee8723a64ef177068a00e475520cf4e4fa06cf`.

The corresponding planner admission passed and the canonical Stage 3 resume
completed HIR collection. It again reported exactly 117 poisoned modules and
1797 errors across 717 sources. The first `env_get_opt`, `process_run`,
`char_code`, and `MirInstKind` failures remained. The indexed-origin fallback
is valid as a narrow resolver fix, but it did not repair this HIR population.
Stage 3 and the full macOS bootstrap remain unadmitted. This was the second
verify/fix cycle in this session; do not repeat the same run without a new
root-cause fix.

## Function-scope import memo diagnosis

A fail-fast diagnostic using the admitted Stage 2 compiler and Stage 3's
streaming-surface/default-root settings reproduced the first `env_get_opt`
failure. `std.io_runtime` found the re-export route, so the early indexed-origin
fallback was not the limiting step in this case. Temporary logging in an
isolated diagnostic compiler then showed the terminal
`std.nogc_sync_mut.io_runtime` surface declaring `env_get_opt` at callable
position 34. Lazy registration while lowering `env_get` made the local name
bound. After that function scope popped, lowering `home` saw the same name
unbound, but the per-module `registered_import_memo` still contained the tuple
and skipped registration. That is a direct cause of a repeated-function
unresolved-name failure. The top-level facade registration also left the name
unbound despite finding the route; its terminal-index transport remains
unproven and may be a separate defect.

The memo now records whether each completed registration left a live local
binding and skips a repeat only while that binding state still matches. A
focused unit case pops one function scope and requires the same import to bind
in the next. Diagnostic-only logging and an attempted MC/DC clamp were removed
from product source. At this point the repair had not yet received its final
Stage 2/3 admission cycle.

## Third-cycle Stage 2 rejection

The memo-state source linked a third Stage 2 candidate (4 compiled, 766 cached,
0 failed), SHA-256
`ade21c9e39d31d3f9ac812576e9c3867da453a5421bb0657330065e87ca8a58c`.
Canonical sanity rejected it when the positional two-line hello-world native
build crashed with signal 11 at `native_compile 0/1`; the binary is preserved
as `build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`. This verdict
does not identify whether the memo change triggered the crash or merely changed
code layout around the existing positional native-build instability. Stage 3
was not started for this candidate. The focused unit case remains unexecuted
because the admitted bootstrap CLI has no `test` command and the installed
release runner cannot parse current compiler source.

The three-cycle verification cap is exhausted for this session. The memo repair
is unadmitted and must be reviewed on a fresh scoped session before promotion.
The last admitted Stage 2/Stage 3 evidence remains the preceding source
snapshot, whose Stage 3 verdict was 1797 HIR errors.

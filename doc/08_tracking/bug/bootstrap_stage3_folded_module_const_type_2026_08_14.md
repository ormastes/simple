# Bootstrap Stage 3 cannot identify a folded module constant whose type is missing

- **Bug ID:** `bootstrap_stage3_folded_module_const_type_2026_08_14`
- **Date filed:** 2026-08-14
- **Status:** CLOSED — expression-first typing removes the retained Stage-3 failure; Stage 4 remains a separate gate
- **Area:** pure-Simple compiler / bootstrap MIR lowering
- **Severity:** Stage 3 blocker

## Symptom

The preserved render-CLI cycle-7 Stage 3 run loaded 897 sources, parsed all 616
closure modules, completed HIR and monomorphization, and then emitted the same
diagnostic 14 times:

```text
error: bootstrap MIR lowering: cannot derive module constant type from folded value; add an explicit annotation
```

This is a real Stage 3 system failure, but the diagnostic contains no source
path, source anchor, symbol, module, constant name, or folded-value kind. The
current evidence therefore cannot name the failing constant. Guessing a source
annotation from the message would be mutation before localization, not a fix.

## Preserved evidence

The evidence is owned by the isolated `restart12-render_cli` bootstrap lane:

- `/mnt/data/worktrees/restart12-render_cli/build/restart12-render-cli-pass2/stage3-cycle7.log`
- `/mnt/data/worktrees/restart12-render_cli/build/restart12-render-cli-pass2/stage3-cycle7.events`

The event receipt records source closure `616/616`, load `897/897`, parse
`616/616`, HIR complete, and monomorphization complete. The log then records 14
unanchored folded-module-constant diagnostics. It does not record a successful
terminal event or a Stage 3 candidate identity.

## System reproducer

The production-shaped reproducer is Stage 2 compiling the real bootstrap entry
and its full source closure as Stage 3, with stub fallback disabled. Cycle 7 used
the isolated render-CLI lineage and produced the two artifacts above. Its
equivalent command shape is:

```text
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_ARENA_DECLS=1 \
SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NO_STUB_FALLBACK=1 \
<cycle-7-stage2>/simple native-build \
  --target x86_64-unknown-linux-gnu --backend llvm \
  --runtime-bundle core-c-bootstrap --threads 2 \
  --cache-dir <cycle-7-stage3-cache> --mode dynload \
  --runtime-path <cycle-7-stage2-runtime-authority> \
  src/app/cli/bootstrap_main.spl -o <cycle-7-stage3>/simple
```

This is a reconstruction of the preserved cycle's system boundary, not a claim
that an exact shell transcript was retained. The log and event receipt are the
authoritative reproduction evidence. Do not rerun the expensive full closure
merely to rediscover the same unanchored message.

## Required Integration reproducer

Before changing compiler semantics, add the smallest owning-boundary Integration
SSpec that:

1. constructs or compiles a module constant whose expression is folded;
2. reaches the same bootstrap MIR type-derivation path;
3. reproduces this failure mechanism with a source anchor and constant identity;
4. turns green only when the identified constant type is preserved or derived
   correctly.

If a reduced fixture cannot reproduce the same mechanism, return to debugging
the system evidence and improve the diagnostic at the failure site. Adding
adjacent constant-folding tests is not a substitute for a faithful reproducer.

## Integration attempt and source candidate

`test/02_integration/compiler/bootstrap_stage3_folded_module_const_type_spec.spl`
was attempted three bounded times with the available Rust seed. The apparent
native-build success and empty executable output were not compiler evidence:
the imported generic `process_run` collided with `app.io.mod_stub` and returned
synthetic empty success; no output artifact existed. This is recorded as
`integration_process_run_stub_false_success_2026_08_14`. The reproducer now
uses the uniquely named live bounded process owner, but the iteration guard
forbids another run in this session. The Stage 3 mechanism therefore remains
unreproduced at Integration level; no adjacent tests are justified.

Source inspection proves `lower_const_expr` can fold only scalar Int, Float,
Bool, Str, or integer Binary values here. `mir_const_value_type` already names
those scalar variants, so the Stage 3 failure is consistent with a self-hosted
folded-enum identity/match failure. The current candidate derives the type from
the authoritative originating HIR expression before falling back to the folded
value and includes the constant name in any remaining fatal diagnostic. A
source check was started successfully but the seed runner did not emit a final
verdict; no Stage 3 proof exists yet.

## Fresh scoped Integration evidence (2026-08-14)

The corrected reproducer was exercised for three bounded cycles through the
repository `bin/simple` release path with `SIMPLE_NO_STUB_FALLBACK=1`. The child
resolved to `bin/release/x86_64-unknown-linux-gnu/simple`, but emitted the
mandatory warning that it is Rust-seed-built. These runs are diagnostic
Integration evidence and cannot qualify Stage 4.

Cycle 1 accepted the native-build result and obtained exit code zero from the
program, but captured empty stdout. The fixture's bare `print VALUE` form was
changed to the native fixture call convention, and the SSpec gained an
immediate `file_exists(OUTPUT)` gate. Cycle 2 proved the artifact existed before
execution and still observed exit code zero, empty stderr, and empty stdout.
Cycle 3 used the byte-oriented native regression convention `println(VALUE)`;
it produced the same empty stdout and failed the exact output assertion. All
three cycles failed 1/1, so the iteration cap is exhausted.

This does **not** reproduce the Stage-3 folded-value diagnostic. It shows that
this seed-assisted native-build boundary can report success, materialize a
runnable artifact, and return zero while producing none of the fixture's
observable output. No adjacent constant-folding tests are justified. A later
investigation must preserve the artifact inside the scenario, inspect its entry
symbol/code map, and distinguish `main` selection, native output lowering, and
worker output selection before retrying this SSpec.

## Next debugging observation

Instrument the existing error emission with the module/source anchor, constant
name or stable symbol ID, declared/inferred type, and folded-value kind. Preserve
the raw cycle evidence. Once the constant is named, reduce it to the Integration
SSpec, determine whether the defect belongs to folding, type propagation, the
flat/HIR-to-MIR bridge, or diagnostics, and only then implement a root-cause fix.

## Verification boundary

- A source fix candidate exists but is not yet Stage-3 verified.
- The Integration attempt did not reproduce the original compile mechanism.
- The fresh Integration follow-up exhausted three bounded cycles: an artifact
  existed and returned zero, but exact stdout remained empty.
- No Stage 3 candidate was admitted from cycle 7.
- **No Stage 4 build, qualification, deployment, or PASS is claimed.** Stage 4
  must remain blocked until a fixed Stage 3 completes its provenance and
  admission gates.

## Read-only forensic closure (2026-08-14)

Later retained evidence establishes the compiler owner and supersedes the
earlier statement that the root cause was unknown.  No build was launched for
this audit.

The cycle-7 log reaches `[bootstrap-flat-entry] index=0 modules=616
functions=26` after monomorphization.  In the source identity used by that
cycle, the failing path is:

1. `CompilerDriver.aot_compile` selects
   `bootstrap_lower_to_mir_context` for pre-Stage-4 bootstrap AOT;
2. closure mode selects
   `bootstrap_lower_flat_hir_modules_to_mir_for_target`;
3. `bootstrap_lower_flat_hir_module_to_mir` iterates the flat module's
   constants and calls `MirLowering.lower_const`;
4. `lower_const_expr` successfully folds a scalar initializer, but the
   unresolved HIR type sends the folded payload to `mir_const_value_type`;
5. the second native payload-enum match falls through, `error_fatal` records
   the diagnostic, and `bootstrap_reject_fatal_mir_errors` prints the fourteen
   messages before exiting.

The actual Stage-2 ELF resolves `lower_const_expr` to
`compiler__mir___MirLoweringExpr__method_calls_literals__MirLowering.lower_const_expr`
(not the adjacent duplicate source body in `literals.spl`) and contains the
symbols `MirLowering.lower_const` and `MirLowering.mir_const_value_type`.

The identity mismatch is exact:

- cycle-7 `source-inputs-before.txt` records
  `src/compiler/50.mir/_MirLowering/function_lowering.spl` as SHA-256
  `b54e7931bdac787c7c1259646988bf283c1360346304d9ac3d339bd15a6d3ae9`,
  exactly the pre-fix `8a27fa62644` source;
- the retained Stage-2 compiler is
  `stage2-cycle5/x86_64-unknown-linux-gnu/simple`, SHA-256
  `e3ae9475088ed2fe8edceb4e14f8b2db336ad8db8920d516d3dc8f99c6cf3dfc`,
  and its ELF contains `mir_const_value_type` plus the old unnamed diagnostic;
- the expression-first repair is commit `683e2d1009e`, whose owner-file
  SHA-256 is
  `fbda79c08508a44b49fd62051bcf23a723bdcdce8a243d74f2082544617cd724`.
  It postdates cycle 7 and therefore cannot be evaluated by replaying the
  retained stale authority.

The minimal semantic repair is the one in `683e2d1009e`: derive the MIR type
from the authoritative originating `HirExpr.kind` (Int, Float, Bool, String,
or integer Binary) before any compatibility fallback to `MirConstValue`, and
use the helper from both constant and static lowering.  A later strict Stage-3
bootstrap retained in
`stage3_runtime_error_static_owner_receiver_corruption_2026-08-14.md` clears
all fourteen diagnostics and reaches the later `runtime_error` frontier,
which is system-boundary verification of this repair.  Cycle 7 still cannot
identify the fourteen constant names because its diagnostic omitted them.

The smallest faithful Integration reproducer should contain only five
unannotated module values (integer, float, bool, text, and an integer binary
expression), compile them with an admitted pure-Simple compiler under
`SIMPLE_NO_STUB_FALLBACK=1`, execute the candidate, and assert exact output
such as `41:2.5:true:folded:42`.  The constants in
`test/fixtures/native_method_resolution_payload_enum/main.spl` already provide
this matrix but are mixed with unrelated method-resolution cases; extracting
that matrix is stronger than the unit-only `classify_folded_value` test, which
does not traverse `lower_const` and is not a faithful reproducer by itself.

## Current-main fix and branch evidence

Current main uses one `mir_folded_const_type` decision owner from both
`lower_const` and `lower_static`. It selects Int, Float, Bool, String and
integer Binary types from `HirExprKind` before compatibility fallback for Int,
Float, Bool, Str and Zero folded values; aggregate fallback fails closed.

- Unit branch matrix: 2/2 PASS, covering 11/11 logical branches.
- Parser→HIR→MIR Integration: 1/1 PASS for inferred integer, zero, float, bool,
  text and folded binary constants with exact name/type/value-kind rows.
- The one-shot source checker exceeded its 180-second watchdog without a
  semantic diagnostic; this is unavailable checker evidence, not a PASS.
- The pure-Simple native System SSpec blocks a Rust seed and remains pending an
  admitted compiler.

The retained strict Stage-3 receipt proves the fourteen original errors vanish
with the expression-first repair and compilation advances to the independent
`runtime_error` frontier. Stage 4 itself remains unadmitted.

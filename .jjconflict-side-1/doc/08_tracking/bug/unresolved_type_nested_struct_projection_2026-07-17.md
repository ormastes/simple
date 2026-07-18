# Unresolved type corrupts nested struct projection

## Reproduction and corrected diagnosis

In `_engine2d_draw_ir_render_commands`, a loop-local `val x = offset_x +
command.x` is correct at its definition but is reloaded from another stack
slot when passed later to `_engine2d_draw_ir_render_box` in an AArch64 native
build. The first HTML rectangle has `command.x == 0`, while LLDB observes the
callee receiving `x == 0xffffffff8714f8a1`; every rectangle is consequently
clipped outside the framebuffer.

The apparent stack-slot mismatch was downstream of an invalid type annotation:
`batch.embedding` was annotated as `DrawIrEmbedding`, while the schema defines
`DrawIrEmbeddingConfig` and no `DrawIrEmbedding` declaration or alias exists.
The unresolved imported name was silently accepted; `.x` then defaulted to
field index zero and returned the embedding object pointer. LLDB observed that
pointer arriving as `_engine2d_draw_ir_render_commands` argument `offset_x`.
The executor now uses the real `DrawIrEmbeddingConfig` type.

A second erased-type defect remained after that correction. Array-parameter
metadata correctly recovered each `DrawIrCommand` element's struct layout, but
the projection `command.kind` still defaulted to MIR `i64` because the HIR
field expression carried no inferred type. Native equality consequently
compared a raw text pointer with a tagged text value, skipped all four valid
commands, and reported the kind as `<value:pointer>`. MIR struct prescan now
records declared `text` field representation and both field-dispatch paths
emit those projections as `Opaque("str")`. The change self-hosted through two
successive pure-Simple bootstrap compilers (711 compiled, 0 failed each); the
renderer regression remains the next bounded verification step.

## Required compiler fix

Reject unresolved names in grouped `use` imports and explicit annotations, and
add a native regression proving a nested struct field projection retains its
declared struct type across a function boundary. The compiler must diagnose a
misspelled imported type instead of silently resolving subsequent fields to
index zero. The regression must also cover a `text` field projected from a
struct decoded from a typed array parameter and compared with a text literal.

## 2026-07-17 native verification result

The renderer verification still fails after the declared-text and
array-parameter metadata changes. The producer can inspect the same four
commands and prints `kind=rect is_rect=true`, but after
`batch.commands` crosses into `_engine2d_draw_ir_render_commands`, all four
`command.kind` projections remain raw pointers. The executor reports
`rendered=0 skipped=4` and formats the unsupported kind as `<value:pointer>`.

Two source-level controls did not change the result:

- indexing `commands` and explicitly binding `val command: DrawIrCommand`
- explicitly binding `val commands: [DrawIrCommand] = batch.commands` before
  the free-function call

A completely fresh entry-closure cache (`198 compiled, 0 cached`) produced the
same failure, disproving stale incremental interface metadata as the cause.
The remaining compiler regression therefore needs to exercise a nested array
field passed to a typed array parameter, followed by a struct `text` field
projection in the callee. The declared text representation is either not
attached to the decoded element local or is lost before equality lowering.

## 2026-07-17 focused import probe

A minimal two-module fixture now covers the intended boundary at
`test/fixtures/native_nested_struct_array_text_projection/`: an exported
provider owns a command with a `text` field and a batch with a command array;
the consumer passes `batch.commands` into another function and compares the
loop element's field. Its native result is `5` with exit code `0`, so the
general imported-struct path is valid.

Inspection then found that `draw_ir_adv.spl` used `DrawIrCommand` in parameter
annotations without listing it in the grouped import from `common.ui.draw_ir`.
The missing import was added. A cache-preserving renderer rebuild still
reported four pointer-valued command kinds; because the provider module was
one of 196 cached units in that run, a fresh-cache build with the corrected
import is required next to distinguish stale interface hydration from a
Draw-IR-specific provider/export problem.

## 2026-07-17 fresh-cache and exact-provider result

The corrected-import renderer was rebuilt in a new isolated cache with `198
compiled, 0 cached`; it still skipped all four commands with pointer-valued
kinds. Stale provider/interface hydration is therefore ruled out.

Two increasingly exact native probes are green:

- the real imported `DrawIrCommand` returned by `draw_ir_rect`, passed as
  `[DrawIrCommand]`, compares `command.kind == "rect"` and exits `0`
- the real `DrawIrComposition.batches -> DrawIrBatch.commands ->
  [DrawIrCommand]` by-value call chain also returns `result=1` and exits `0`

These results rule out Draw IR visibility, the command's large field layout,
nested array-field projection, and composition/batch value-copy boundaries in
isolation. The unresolved boundary is now specific to the Engine2D executor
context: `_engine2d_draw_ir_render_commands` takes an `Engine2D` struct before
the command-array parameter and returns an aggregate containing `Engine2D`.
The next compiler probe should reproduce that multi-aggregate signature and
inspect which parameter local receives `array_element_struct_syms`, rather
than changing Draw IR exports or retrying the full renderer unchanged.

## 2026-07-17 Engine2D executor isolation

The real Engine2D signature was tested directly in an isolated native fixture:

- `fn (Engine2D, [DrawIrCommand]) -> Outcome(engine: Engine2D, count: i64)`
  returns `result=1`
- `engine2d_draw_ir_adv_batch` renders the same command with
  `rendered=1 skipped=0`
- `engine2d_draw_ir_adv_composition` traverses a real `DrawIrComposition` and
  returns `composition_rendered=1 composition_skipped=0`

All three paths exit `0`. This rules out the Engine2D-leading parameter,
Engine2D-containing aggregate return, the executor module, and its batch and
composition traversal. The failing value is specifically the composition
returned by `simple_web_layout_render_html_draw_ir`. The next bounded probe
must feed that browser-produced composition to an offscreen/software executor
in the same small binary; if it reproduces, inspect the web renderer's return
and nested array construction provenance rather than the Draw IR consumer.

## 2026-07-17 Metal branch isolation

The browser-produced composition is valid on the software executor:
`producer=4 rects=4 rendered=4 skipped=0`, exit `0`. Switching only the engine
to `Engine2D.create_with_backend_fast(..., "metal")` reproduces the failure:
`producer=4 rects=4 rendered=0 skipped=4 source=device_readback`.

A local executor in that same Metal binary, with the same leading `Engine2D`,
`[DrawIrCommand]`, offsets, resolved-image array, blend flag, engine method
queries, and Engine2D-containing aggregate return, still counts all four
rectangles. Thus Metal construction and the function ABI are not sufficient
to corrupt the commands.

The web root batch declares `surface_id="html"`, `(x,y)=(0,0)`, dimensions
equal to the viewport, opacity `1000`, and clipping enabled. Software always
uses the direct path here; Metal can enter the shared-offscreen branch if
`fills_target_exactly` evaluates false. The next probe should compare the
executor-visible engine/embedding dimensions and run the same commands with
an empty surface id (forcing direct rendering). This will distinguish a bad
full-target predicate/projection from corruption inside
`create_shared_metal_offscreen` or the child composite path.

## Resolution

Forcing an otherwise identical full-target batch to use an empty surface ID
rendered all four commands on Metal with device readback. The original browser
embedding was independently observed as `(0,0,320,240,1000)`, proving it should
have taken the existing full-target direct-render short circuit.

The compact predicate mixed nested embedding field projections with
`Engine2D.width()`/`height()` method calls in one boolean expression. Native
lowering mis-evaluated it on the browser/Metal path. The executor now
materializes typed target and embedding scalar locals and evaluates three
simple intermediate booleans: origin match, size match, and full opacity.

Canonical native evidence after the fix:

- `rendered=4 skipped=0 fallback=false`
- `readback_source=device_readback`
- 76,800 ARGB pixels, all nonblank
- exact samples: white `4294967295`, blue `4280640491`, red `4293870660`,
  green `4280468830`

The emitted artifact identifies
`simple-web-core-renderer-metal-gpu-readback`, resolves backend `metal`, and
sets `gpu_backend_used=true`. The focused browser/Metal fixture now retains
the original surfaced batch and requires all four commands to render, so the
short-circuit regression cannot be hidden by forcing an empty surface ID.

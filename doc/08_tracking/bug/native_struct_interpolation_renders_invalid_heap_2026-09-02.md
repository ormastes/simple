# Interpolating a struct in native codegen silently renders `<invalid-heap:0x...>`

**Date:** 2026-09-02
**Status:** FIXED (runtime rendering, 2026-09-02) — see §Resolution. NO REGRESSION GUARD EXISTS for it yet.
**Severity:** HIGH — silently destroys diagnostics, and does so only on failure paths

## What happens

`"{some_struct}"` in native-compiled Simple does not render the struct's fields
and does not fail. It emits the literal text `<invalid-heap:0x{pointer:x}>`.

Mechanism, exactly:

- `src/compiler_rust/runtime/src/value/heap.rs:8` — `HeapObjectType` has
  **no `Struct` variant**: String 0x01, Array 0x02, Dict 0x03, Tuple 0x04,
  Object 0x05, Closure 0x06, Enum 0x07, Future 0x08, ... A native-codegen
  struct pointer therefore carries no header the runtime recognises.
- `src/compiler_rust/runtime/src/value/sffi/io_print.rs:474` —
  `heap_value_to_display_string` takes its
  `let Some(object_type) = v.heap_type() else { return format!("<invalid-heap:0x{:x}>", ...) }`
  arm and returns that string.

A CLASS instance renders as `<object@0x...>` (`io_print.rs:562`) — also useless
but distinguishable. The `invalid-heap` spelling is the fingerprint of a
**struct**.

## Why it matters

It cost a day of Windows-bootstrap investigation. The Stage 2 receiver gate
reported

```
Linking failed: Windows MSVC linking failed: <invalid-heap:0x1e9548829b1>
```

from `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:877`,
which interpolated `{e}` where `e` is a `LinkError` **struct**
(`70.backend/linker/link.spl:108`). The linker's real message
(`e.message`) was never read. Multiple prior investigations reasoned about a
message the code never asked for. See
`stage2_receiver_link_error_text_is_invalid_heap_2026-09-02.md`.

Second live instance found in the same sweep:
`_LinkerWrapper/shared_linking.spl:293` (`"Windows MSVC DLL linking failed: {e}"`).
Both are now `{e.message}`.

The failure mode is structurally nasty: `"{err_struct}"` appears overwhelmingly
on ERROR paths, so it only fires once something else has already gone wrong,
and it converts that failure into an undiagnosable one.

## Not established

- How many other `"{struct}"` sites exist in the tree. No census has been run.
  A census is the obvious next step and needs type information, so a grep alone
  will not do it.
- Whether the interpreter renders these correctly (it appears to), which would
  make this an interpreter/native divergence as well as a diagnostic loss.

## Fix options (not yet chosen)

1. **Compile-time**: make interpolating a struct with no display an error, or a
   lint. Cheapest to reason about; forces the author to name a field.
2. **Runtime**: give structs a heap header and a field-wise render, matching
   the interpreter. Larger, but removes an interpreter/native divergence.
3. Minimum viable: a lint rule flagging `{ident}` where `ident`'s type is a
   struct without a display, in the same family as `cow_alias_hotpath`.

There is currently **no guard of any kind** for this class.


---

## Measured corrections (2026-09-02, Windows host, `bin/simple.exe`)

Three claims above were re-measured by EXECUTION and two of them are wrong.
Repro: a `LinkError` struct, a class, and a tuple interpolated in one file, run
with `bin/simple.exe run`.

```
struct: <invalid-heap:0x29818c4d611>
class:  <invalid-heap:0x29818c32051>
tuple:  (1, two)
field:  MSVC link.exe not found
```

1. **A CLASS renders `<invalid-heap:...>` too, NOT `<object@0x...>`.** The
   "`invalid-heap` is the fingerprint of a struct" claim in this record is
   **false** on the JIT lane: `heap_type()` returns `None` for a class instance
   as well. Do not use the spelling to identify the receiver kind.
2. **The interpreter is clean.** All four receiver kinds render without the
   blob under `simple test` (tree-walk), so this is a genuine
   interpreter/native divergence, as suspected. Pinned by
   `test/01_unit/runtime/interpolation_receiver_matrix_spec.spl`.
3. **`SIMPLE_ENGINE_RECEIPT=1` produces no receipt on this seed.**
   `strings bin/simple.exe | grep -c SIMPLE_ENGINE_RECEIPT` -> `0`. No engine
   receipt can be quoted for any measurement on this binary; the lane is
   identified by the command (`run` = JIT, `test` = interpreter) instead.
4. **Second divergence found in passing:** `"...{e.message}"` — a member access
   written directly inside an interpolation — renders correctly on the JIT but
   fails on the tree-walk interpreter with ``semantic: variable `e` not found``.
   Separate defect; not fixed here.

## Census (2026-09-02) — UPPER BOUND

Method: one tree-wide awk pass over 16,220 non-vendored `src/**/*.spl`.
Pass 1 builds a type-kind map from `(pub )?(struct|class|enum) Name`
declarations (8,108 struct / 6,778 class / 1,895 enum names unique by kind;
**553 names are declared with more than one kind in different files** and are
reported as `AMBIG`, never silently assigned). Pass 2 resolves, per file and
with `"""` docstrings skipped, `val|var x = Type(` and `x: Type` bindings, then
classifies every `{bare_identifier}` interpolation by that binding's kind.
Wrapper names over runtime primitives (`text`, `String`, `i64`, ...) are
excluded — `text` alone accounted for 11,696 hits and renders correctly.

| receiver kind | interpolations | of which on an error path |
|---|---|---|
| struct | **122** | 32 |
| class | 50 | 14 |
| enum | 110 | 50 |
| ambiguous name | 77 | 18 |
| unresolved (`UNKNOWN`) | 53,202 | — |

**This is an upper bound and also an under-count, and both directions were
verified by hand** (per `doc/07_guide/infra/detector/detector_standard.md`):

- *Over-counts*: the type map is tree-wide but a binding is resolved
  per-file, so a local name that collides with an unrelated type elsewhere is
  misattributed. Confirmed on `70.backend/linker/lib_smf_reader.spl:141`
  (`{module_name}` is `text`; the `Module` reading came from a docstring
  before docstrings were skipped, and residual same-shape errors remain).
- *Under-counts*: 53,202 interpolations could not be typed at all
  (cross-module types, generics, method-call receivers, `?`-unwrapped values).
  Interpolations of non-bare expressions (`{f(x)}`, `{a.b}`) are not counted.

Verified TRUE positive, error path, in the interpreter's own environment:
`src/app/interpreter/core/environment.spl:128` and `:235` —
`Err("Undefined variable: {name}")` where `name: SymbolId` is a struct.
Highest-risk error-path sites also include
`30.types/dim_constraints.spl:594,605,616,642` (`DimExpr` interpolated into the
generated assertion text), `70.backend/backend/lean_mir_translate.spl:807-820`
(`MirOperand` in four `Err(...)` messages), and
`lib/nogc_sync_mut/replay/container/checkpoint_format.spl:303,321`.

## Resolution (2026-09-02)

**Chosen: make the runtime rendering self-describing, keeping the marker** —
`src/compiler_rust/runtime/src/value/sffi/io_print.rs`, the ONLY two emitters
of the string in the whole tree (the C runtime under `src/runtime/**` has
none). Both arms now render

```
<invalid-heap:0xADDR (unrecognised heap header -- typically a struct or class value, which has no display rendering: interpolate a field instead, e.g. {x.message}; otherwise a mis-tagged non-pointer)>
<invalid-heap:0xADDR (heap header says String but the payload is unreadable)>
```

**The `<invalid-heap:` prefix is deliberately RETAINED, and a first attempt
that renamed it to `<no-display:` was reverted.** Five existing specs use that
exact spelling as the fingerprint of a *tag-escape* defect and assert
`contains("<invalid-heap:") == false`:
`test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl:100,102`,
`tag_escape_surfaces_detection_spec.spl:126,128`,
`wide_int_box_roundtrip_class_spec.spl:164,165`,
`chained_call_receiver_class_spec.spl:108`, and
`test/01_unit/compiler/backend/llvm_ir_builder_target_header_lifetime_spec.spl:54,74`.
Renaming would have turned all five vacuously green while the defects they
guard stayed live — the fix would have silently destroyed five detectors while
fixing one. The defect was never the prefix; it was that the prefix was the
ENTIRE message and named no cause. All four affected specs re-run green on the
rebuilt seed (3/3, 5/5, plus 4/4 and 6/6 for the new ones), and the raw-`9`
tag-escape probe still reports `PACKED_BITFIELD_READ PROBE: ALL PASS`.

**Why this one, over the two alternatives:**

- *Field-wise struct display* (add a `Struct` heap variant) is the most useful
  outcome and was rejected on cost and blast radius: it is a heap-ABI change
  requiring a header at every struct allocation site plus per-type field-name
  metadata that does not exist at runtime today, landed while other agents are
  live on the bootstrap. It also would not have covered the CLASS half, which
  measurement showed shares the defect.
- *Compile-time error on interpolating a struct* would be the strongest
  correctness bar but cannot fire without a seed redeploy, breaks 122+ existing
  sites at once, and — decisively — the census cannot adjudicate those sites,
  so the error would land on code nobody has classified.
- *A lint rule* (the `cow_alias_hotpath` model) receives ONE FILE's text
  (`check_cow_alias_hotpath(content, path)`): it cannot resolve
  `name: SymbolId` in `environment.spl`, where `SymbolId` is declared in
  another module, so it would miss the one hand-verified true positive. Worth
  adding once type information reaches lint rules; it is not the smallest thing
  that stops the silent destruction.

The chosen fix stops the *silence* — which is the whole defect — at every site
at once, with no source changes and no breakage, and satisfies the hard
requirement that `<invalid-heap:0x...>` never again be the entire content of a
user-facing message without naming its cause.

**Cross-platform:** `io_print.rs` is shared by every target, so the new text
appears identically on Linux, macOS, FreeBSD and Windows. Unix behaviour
changes only in that the same defect renders the same longer text — no other
output moves (tuple, field, int, float, array, dict renderings are
byte-identical before and after). POSIX could not be executed on this host
(Windows only); the change is platform-independent Rust `format!` with no
`cfg` branches and no platform-conditional call sites.

**Specs:** `test/01_unit/runtime/struct_interpolation_display_spec.spl`
(reproducing) and `test/01_unit/runtime/interpolation_receiver_matrix_spec.spl`
(generalizing across struct/class/enum/tuple).

### Verification by execution (2026-09-02)

Seed rebuilt from this change:
`src/compiler_rust/target/x86_64-pc-windows-msvc/release/simple.exe`
(md5 `6d1fdbeb22249db2b8c5121bfb69e70d`), compared against the deployed
`bin/simple.exe` (md5 `d52d770724a9f8797e98ac7819709ab9`).
**`bin/simple.exe` was NOT replaced — every deployed binary predates this fix,
and nothing changes for users until a seed redeploy.**

```
=== BEFORE (bin/simple.exe run) ===
struct: <invalid-heap:0x2a50c1a3541>
class:  <invalid-heap:0x2a50c1c2141>
tuple:  (1, two)
field:  MSVC link.exe not found

=== AFTER (rebuilt seed, same source) ===
struct: <invalid-heap:0x19e3eb94331 (unrecognised heap header -- typically a struct or class value, which has no display rendering: interpolate a field instead, e.g. {x.message}; otherwise a mis-tagged non-pointer)>
class:  <invalid-heap:0x19e3ebb06b1 (unrecognised heap header -- typically a struct or class value, which has no display rendering: interpolate a field instead, e.g. {x.message}; otherwise a mis-tagged non-pointer)>
tuple:  (1, two)
field:  MSVC link.exe not found
```

Rust unit tests: `cargo test -p simple-runtime --release --lib -- io_print`
-> 27 passed, 0 failed (the two forged-heap tests now assert BOTH that the
prefix survives and that a cause is named).

Landing note: `test/unit/runtime/` exists alongside `test/01_unit/runtime/`, so
whoever lands this hits `check-test-tree-divergence.shs`; use the scoped-delta
escape (`check-test-tree-divergence-delta.shs BASE NEW`) and record the
pre-existing offender list per `.claude/rules/vcs.md`.

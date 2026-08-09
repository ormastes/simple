# `native-build` MIR lowering: cross-module `Result<T, E>` payload struct-name recovery collides/misses across modules — 4th/5th layer RESOLVED, 6th/7th layer surfaced (still open, root cause narrowed to a SymbolTable id-divergence between HIR- and MIR-lowering-time views)

## Summary

Follow-up to
`doc/08_tracking/bug/native_build_instance_method_dispatch_unresolved_after_match_bind_2026-08-09.md`
(3rd layer, RESOLVED by commit landed alongside this doc — see that doc's
resolution note). That fix made a **single-module** `val h = match
FileHandle.open(...): case Ok(hh): hh ... ` compile clean under native-build:
the match-arm merge-copy now propagates `struct_value_syms` from the bound
payload local to the match's own result local, so `h.write_text(...)` etc.
dispatch correctly.

With that fix landed, the real `rt_io_file_roundtrip` fixture (real stdlib
`FileHandle`/`File` from `src/lib/nogc_sync_mut/io/file.spl`, imported via
`use`) **still fails identically**: same `unresolved method call:
write_text/close/read_text/size/read_all/write_all/merge` errors, same
count (17), in the full ~18-minute closure build. Root cause is a DIFFERENT,
deeper bug in the same neighbourhood: cross-module struct-name recovery for
`Result<T, E>` payloads.

## Root cause (two contributing mechanisms, both confirmed empirically)

1. **`enum_payload_struct_names` is a GLOBAL, unqualified `"{enum_name}::
   {variant}"` map** (`switch_operators_calls.spl`). Every `Ok(SomeStruct(...))`
   construction site in the WHOLE compiled closure writes the same key
   (`"Result::Ok"`) — there is no per-instantiation disambiguation (no `T` in
   the key). With N different `Result<T, E>` instantiations in one closure
   (real stdlib code has dozens), only the LAST one MIR-lowered wins, and
   every earlier `case Ok(x): x.method()` for a different `T` silently
   resolves to the wrong struct name or none. Proven with a minimal
   **single-module** 2-struct repro (`Other.make() -> Result<Other, text>`
   lowered before `FileHandle.open() -> Result<FileHandle, text>`): `o.bump()`
   (the earlier-lowered struct's method) fails unresolved while
   `h.write_text()`/`h.close()` (the later-lowered struct) succeed — swap
   which is lowered last and the failure moves.

2. **Cross-module lowering order defeats the scrutinee-type-based fallback
   too.** A candidate fix (scoping struct-name recovery to the match's own
   `Result<T, E>` scrutinee type via `result_variant_payload_type` /
   `enum_match_expr_type`, immune to mechanism #1's global-map collision by
   construction) still fails to resolve **cross-module**: `FileHandle.open(...)`
   is HIR-lowered as `HirExprKind.MethodCall(receiver=FileHandle, method=
   "open", ..., MethodResolution.Unresolved)` — HIR lowering
   (`20.hir/hir_lowering/expressions.spl`) never constructs the (unused)
   `HirExprKind.StaticCall` variant, so a static-looking call always takes the
   `MethodCall` shape. `enum_match_expr_type`'s `MethodCall` arm resolves a
   static receiver's return type via `self.struct_method_syms["{StructName}::
   {method}"]`, which is populated **per-module inside `lower_module`**
   alongside that module's own body lowering. Entry-closure lowering
   processes the entry module (`main.spl`) BEFORE its dependency module
   (`fh_mod.spl`/`file.spl`) — this exact ordering is the one
   `prescan_module_struct_names` (existing, `module_lowering.spl:726`) was
   built to work around for `struct_field_order` — but that prescan does
   **not** cover `struct_method_syms`. A prescan extension mirroring
   `prescan_module_struct_names`'s pattern (register `struct_method_syms` from
   `module.impls` before lowering any module) was attempted and empirically
   made **no difference** (`struct_method_syms.has("FileHandle::open")` stayed
   `false`) — because `module.impls` is populated only from explicit `impl
   Type: ...` blocks (see `20.hir/hir_lowering/_Items/module_lowering.spl`
   `impls.push`/`module_surface.spl`), never from a `class`'s OWN inline
   methods (`class FileHandle: ... static fn open(...): ...`, the shape both
   the minimal repro and the real stdlib `FileHandle` use). So
   `struct_method_syms` is structurally empty for inline-class-method static
   calls regardless of prescan — this is not just an ordering gap, the source
   data itself is never populated for this declaration shape. That attempted
   fix was reverted (see "Reverted attempt" below) rather than landed as dead
   code.

## Reproduction

**Single-module collision (mechanism #1), fast (~seconds):**
```
class Other:
    v: i64
    static fn make() -> Result<Other, text>:
        Ok(Other(v: 9))
    fn bump() -> Result<i64, text>:
        Ok(self.v + 1)

class FileHandle:
    fd: i64
    static fn open(path: text) -> Result<FileHandle, text>:
        Ok(FileHandle(fd: 1))
    fn write_text(s: text) -> Result<i64, text>:
        Ok(0)
    fn close() -> Result<i64, text>:
        Ok(0)

fn main() -> i64:
    val o = match Other.make():
        case Ok(oo): oo
        case Err(e): return 1
    match o.bump():        # <-- unresolved (Other lowered FIRST)
        case Ok(_): pass
        case Err(e): return 1
    val h = match FileHandle.open("x"):
        case Ok(hh): hh
        case Err(e): return 1
    match h.write_text("hi"):   # <-- resolves fine (FileHandle lowered LAST)
        case Ok(_): pass
        case Err(e): return 1
    print("ok")
    return 0
```

**Cross-module (mechanism #2), fast (~seconds), 2 files:**
```
# fh_mod.spl
class FileHandle:
    fd: i64
    static fn open(path: text) -> Result<FileHandle, text>:
        Ok(FileHandle(fd: 1))
    fn write_text(s: text) -> Result<i64, text>:
        Ok(0)
    fn close() -> Result<i64, text>:
        Ok(0)

# main.spl
use fh_mod.FileHandle

fn main() -> i64:
    val h = match FileHandle.open("x"):
        case Ok(hh): hh
        case Err(e): return 1
    match h.write_text("hi"):   # <-- unresolved even though FileHandle is the ONLY struct
        case Ok(_): pass
        case Err(e): return 1
    match h.close():
        case Ok(_): pass
        case Err(e): return 1
    print("ok")
    return 0
```
Run via the same `native_build_worker.spl --entry-closure` recipe as the
parent doc, with `--source <dir-containing-both-files>` added.

## Reverted attempt (recorded so it isn't retried blind)

Added (then reverted, not landed) to `module_lowering.spl`'s
`prescan_module_struct_names`: a `struct_method_syms` prescan mirroring the
existing `struct_field_order` prescan, sourced from `module.impls` +
`module.functions[].is_static`. Verified via `eprint` instrumentation that
`self.struct_method_syms.has("FileHandle::open")` was still `false` after this
change, for the exact 2-module repro above — confirming `module.impls` is
empty for `class`-with-inline-methods declarations (mechanism #2's real
blocker), not merely unregistered-until-later. A correct fix needs either (a)
inline class methods to ALSO populate `module.impls` (or an equivalent
declaration-only source) during HIR lowering, or (b) `enum_match_expr_type`'s
static-receiver fallback to read directly from wherever inline class methods
actually ARE registered pre-body-lowering (if such a registry exists) instead
of `struct_method_syms`.

## Why this matters for the `rt_io_file_*` AOT stub question

Still genuinely UNDETERMINED. The 3rd-layer fix (arm-merge struct-name
propagation, single-module) is real and verified but does not reach the real
fixture, which is inherently cross-module (`use
std.nogc_sync_mut.io.file.{FileHandle, File}`) and hits mechanism #2 above.
Re-ran the full closure after landing the 3rd-layer fix: identical 17-error
tally, same error signatures, confirming this is a distinct, still-open
blocker rather than a residual of the 3rd-layer bug.

## Next steps

1. Fix mechanism #1 (global-map collision) by keying `enum_payload_struct_names`
   per-instantiation somehow, or by making the scrutinee-type-based recovery
   (`result_variant_payload_type`) the PRIMARY source whenever available
   (single-module case only needs this once mechanism #2 no longer blocks
   cross-module resolution).
2. Fix mechanism #2 (cross-module inline-class-method registration) — likely
   the harder, more load-bearing fix given real stdlib code overwhelmingly
   uses inline `class` methods rather than separate `impl` blocks. Candidate:
   extend HIR lowering to also push a synthesized `module.impls` entry (or
   equivalent) for each class's own methods, so the existing (and any future)
   `struct_method_syms`-based prescan/lookup mechanisms see them.
3. Once both are fixed, re-run the fence script's `RUN_AOT_LEG=1` leg (or the
   exact repro from the parent doc) to get the actual stub/no-stub verdict for
   `rt_io_file_*`.

## Evidence

- Single-module collision repro: exit 1, `unresolved method call: bump` only
  (not `write_text`/`close`) — captured this session.
- Cross-module repro: exit 1, `unresolved method call: write_text` and
  `close` — captured this session, both before and after the reverted
  `struct_method_syms` prescan attempt (identical failure both times).
- Full 18-minute closure re-run of `test/fixtures/rt_io_file_roundtrip/main.spl`
  after landing the 3rd-layer fix: 17 `unresolved method call` errors, byte-
  identical error tally to the pre-fix run documented in the parent doc.

## Resolution (2026-08-09, layer-4 session)

Both mechanisms fixed; both fast repros above now compile clean (EXIT=0, zero
`unresolved method call`, marker-liveness-verified end to end).

1. **Mechanism #1 (global-map collision)** — fixed by making the
   scrutinee-instantiation-derived payload type the PRIMARY source (option 1
   of "Next steps"): at the enum-match single-field bind site
   (`switch_operators_calls.spl`), when `result_variant_payload_type` names a
   Class/Struct, that name is written to `struct_value_syms` for the bound
   payload; the unqualified `enum_payload_struct_names` map is now only the
   last-ditch fallback. No key change needed — the scrutinee type is
   per-instantiation by construction. Single-module repro: `o.bump()` AND
   `h.write_text()` both resolve regardless of lowering order.

2. **Mechanism #2 (inline class methods absent from struct_method_syms)** —
   REAL and REQUIRED for the cross-module repro, but fixed by routing AROUND
   `module.impls`/`struct_method_syms` rather than populating them:
   - `enum_match_expr_type` (MethodCall arm) gained a static-receiver
     fallback through `SymbolTable.lookup_method_in_type` — the symbol table
     DOES carry owner-qualified symbols ("{module}.{Type}::{method}") for
     inline class methods, including imported ones.
   - `method_calls_literals.spl`'s Unresolved INSTANCE arm gained the
     matching fallback: resolve the owner type symbol by the
     `struct_value_syms` NAME via `lookup_or_invalid`, then
     `lookup_method_in_type`.
   - `prescan_module_struct_names` (`module_lowering.spl`) now registers
     every method's declared return HirType in the global name-keyed
     `bootstrap_fn_ret_hir_type` registry under its owner-qualified symbol
     name AND the underscore-sanitized spelling (the importing module's
     symbol table spells module segments with `-` -> `_`; the defining
     module's own symbol keeps the raw directory-derived name — found
     empirically, both spellings must be registered or the importing-side
     name-keyed lookup misses).

## 5th layer surfaced (still open)

The real `rt_io_file_roundtrip` fixture now fails EARLIER, in phase 3 (HIR
lowering): `unresolved type: SeekFrom`, entry module poisoned. NOT caused by
this fix — a control run with the three fixed files reverted to their
pre-fix blobs fails byte-identically — and not present at the layer-3
session's full run, so it arrived via upstream churn between sessions.
Discriminators: `use std.common.io.types.{FileMode, SeekFrom}` alone
compiles; `use std.io.types.{FileMode, SeekFrom}` (file.spl's alias path)
with real SeekFrom pattern-matches compiles; the io.file closure fails even
when the ENTRY drops its own SeekFrom import (the error is attributed to the
entry module regardless). The AOT `rt_io_file_*` stub question therefore
remains UNDETERMINED — never reaches codegen, now for a fifth, pre-existing
reason.

## 5th layer root cause and fix (2026-08-09, layer-5 session)

**Root cause**: `register_imported_type_methods`
(`20.hir/hir_lowering/_Items/module_lowering.spl`) eagerly builds a HIR
callable type for every cross-module method it registers (via
`declared_imported_surface_callable_type` ->
`imported_surface_type_projected`). That resolution requires the method's
param/return type to already have a `bind_qualified_type` binding under the
type's OWN defining module. The sibling code path for composite FIELDS
(`register_imported_symbol`'s `for field in composite.fields` loop, a few
lines above) already recursively pre-registers exactly this kind of
same-module type dependency before lowering field types — but
`register_imported_type_methods` had no equivalent step. A method parameter
type declared in the SAME module as its owning class/impl (e.g. `fn
seek(pos: SeekFrom)` on `FileHandle`, both living in
`src/lib/nogc_sync_mut/io/file.spl`) that was never independently named in
the IMPORTER's own `use` line therefore stayed unbound: the qualified lookup
missed, `imported_surface_type_projected` fell through its scalar
`type_name` branch straight into `lower_named_kind` (bypassing
`imported_surface_type`'s own graceful fallback), and hit the hard,
non-recovered `"unresolved type: {name}"` error path — fatal, and
attributed to whichever module happens to be the CURRENT lowering context
(the entry module), not the type's actual defining module. This explains
every discriminator recorded above: the entry's own SeekFrom import/match
compiles fine because `SeekFrom` gets bound directly; the failure needs a
method whose param/return type is otherwise-unreferenced in the closure.

**Minimal fast repro** (root-caused down from the 18-minute closure to a
sub-second, single-file, ZERO-stdlib-import case — no trait mixin, no enum,
no method call needed):
```
# file_mod.spl
struct Pos:
    off: i64

class FileHandle:
    fd: i64
    fn seek(pos: Pos) -> Result<i64, text>:
        Ok(0)

# main.spl
use file_mod.FileHandle

fn main() -> i64:
    val h = FileHandle(fd: 1)
    print("ok")
    return 0
```
Run via the same `native_build_worker.spl --entry-closure` recipe as above
(`--source <dir-containing-both-files>`). Pre-fix: `unresolved type: Pos`.
Post-fix: `RC=0`. A single-module variant (both declarations in `main.spl`,
method never called) does NOT reproduce — confirms this is cross-module
eager registration, not a general "unused type" gap.

**Fix**: new helper `materialize_imported_callable_type_dependencies`
mirrors the composite-field pattern — for every param and the return type of
a cross-module method being registered, recursively `register_imported_symbol`
any named-type dependency not yet qualified-bound in the type's OWN defining
module, BEFORE calling `declared_imported_surface_callable_type`. Wired into
both call sites in `register_imported_type_methods` (the `impl_.methods` loop
and the `trait_.methods` loop), threading `materialize_enum` through (that
function previously had no such parameter; both of its own call sites already
had `materialize_enum` in scope). Verified with a marker-liveness eprint
probe (`[SEEKFROM-PROBE] register_imported_type_methods ...`) tracing the
exact call chain before writing the fix, then removed before landing.

**Verification**:
- Minimal fast repro above: `RC=0` (was `unresolved type: Pos`).
- The doc's own SeekFrom-with-trait-mixin repro (real enum, `case
  SeekFrom.Start/Current/End` match, `class FileHandle with Seek`): no more
  `unresolved type: SeekFrom`; progresses to a separate, pre-existing,
  unrelated `--emit-object` complaint (`MIR module has no functions`) for an
  enum-only module with zero functions — an artifact of that specific
  minimal fixture, not a regression.
- Layer-1 single-module collision repro and layer-4 cross-module repro
  (reproduced verbatim from this doc's own "Reproduction" section): both
  still `RC=0` — no regression.
- Full 18-minute closure re-run of `test/fixtures/rt_io_file_roundtrip/main.spl`:
  no longer fails in phase 3. `unresolved type: SeekFrom` is GONE. See
  "6th layer" below for where it lands instead.

## 6th layer surfaced (still open, AOT stub question still UNDETERMINED)

With the 5th layer fixed, the full closure build now reaches **phase 4 (MIR
lowering)** — past HIR lowering entirely for the first time in this bug
chain — and fails there with the SAME error signature layer 4 described as
its own root cause: `unresolved method call` for `write_text`, `close`,
`read_text`, `size`, `read_all`, `write_all`, `merge` (18 errors total,
`FileHandle`/`File` instance methods reached through a `case Ok(x): x`
match-bound local).

This is very likely NOT a new, distinct mechanism — it is layer 4's own bug
class (`enum_payload_struct_names` global-map collision / cross-module
`struct_method_syms` gap for inline class methods) reappearing at REAL
closure scale. The layer-4 "Resolution" section above was verified only
against small hand-written fast repros (2-3 `Result<T, E>` instantiations);
it was never run through the actual `rt_io_file_roundtrip` full closure
because the 5th-layer SeekFrom block was hit first, before this session.
The real stdlib closure has dozens of `Result<T, E>` instantiations across
hundreds of modules — evidently enough to defeat the layer-4 fix's coverage
even though this session's isolated regression repros (the exact 2-file
cross-module case from layer 4's own "Reproduction" section) still pass
clean. Filing this as a 6th layer rather than reopening layer 4's "Resolution"
note verbatim, since the exact failure surface at full-closure scale has not
yet been isolated to a minimal fast repro.

**AOT `rt_io_file_*` stub verdict: still UNDETERMINED.** The closure now
gets one phase further (4 instead of 3) but still never reaches codegen.
Next step for a follow-up session: bisect the full closure's actual
`Result<T, E>` instantiation graph (not another hand-written repro) to find
what specifically defeats the layer-4 fix at scale — likely a global-map
key collision or an ordering case the small repros do not exercise.

## 7th layer (this session, 2026-08-09): the fast repro does NOT actually
pass clean — corrects the 6th-layer note above

The 6th-layer note above states "this session's isolated regression repros
(the exact 2-file cross-module case from layer 4's own 'Reproduction'
section) still pass clean." Re-running that EXACT repro shape this session
(fresh 2-file `fh_mod.spl`/`main.spl`, plain class, no traits, hyphen-free
scratch path to avoid the unrelated `_hir_symbol_owner_module` vs.
`hir_module_logical_name_from_path` sanitization confound) reproduces
`unresolved method call: write_text` / `close` — it does NOT pass clean.
This session's task began from a hypothesis (inline `with Trait:` shape is
the missing piece) that is also FALSIFIED: a plain class with no trait
mixin reproduces the identical failure, so traits are not the
differentiator.

Root-caused via targeted `eprint` instrumentation (added, and fully reverted
before landing — no functional change shipped this session):

1. `FileHandle.open(...)`'s static call resolves fine end to end
   (`enum_match_expr_type`'s static-receiver fallback works).
2. Its declared return type correctly lowers to `HirTypeKind.Result(ok_type,
   err_type)` (layer-4's mechanism-#1 fix works).
3. But `ok_type`'s `HirTypeKind.Named(SymbolId)` — built via
   `declared_imported_surface_callable_type` ->
   `imported_surface_type_projected` -> `self.lower_type` ->
   `lower_named_kind("FileHandle", ...)` — resolves to the WRONG symbol at
   MIR-lowering time: instrumentation showed `self.symbols.get_symbol_raw(
   rpt_sym.id)` (in `switch_operators_calls.spl`, MIR layer) returning a
   `Method` symbol (`FileHandle::close`) at the exact numeric id that, when
   checked LIVE during HIR lowering of the SAME module moments earlier (6
   repeated `lower_named_kind("FileHandle")` calls, all agreeing), correctly
   named the `FileHandle` Class.
4. This is a **snapshot-timing / instance-divergence** bug, not a simple
   lookup-priority bug: `self.symbols` as mutated live during HIR lowering
   and `HirModule.symbols` as read at the START of MIR lowering
   (`_MirLowering/module_lowering.spl:863`, `self.symbols = module.symbols`)
   disagree about what the SAME numeric id names, for the SAME module.
   Printing `module.symbols.get_symbol_raw(1)` at MIR's `lower_module` entry
   for both closure modules confirmed each module's SymbolTable carries its
   OWN independent id sequence (expected — module-scoped tables), but
   `main.spl`'s (the importing module's) own sequence differs between the
   live HIR-time view and the MIR-time view of what should be the identical
   object (`SymbolTable` is a `class`, i.e. reference type, in this
   language, so this is not ordinary value-copy divergence).
5. Three targeted fixes were written and verified NOT to change the
   outcome (all reverted, not landed):
   - Extending `SymbolTable.define()`'s existing type-symbol first-write-wins
     check to also consult the global `exact_symbols` index (not just the
     scope-local `scope.symbols` map).
   - Extending that same global dedup to qualified (`"::"`-containing)
     Method/Function names, matching `register_imported_type_methods`'s own
     (apparently equally scope-chain-blind) `lookup_or_invalid(...)
     .is_valid()` idempotency guard.
   - Making `lower_named_kind`'s type-position lookup prefer the
     kind-checked global `lookup_exact_type` over the scope-walking
     `lookup_or_invalid`.

   All three measurably stabilized the LIVE HIR-lowering-time view (6/6
   consistent, verified via instrumentation) but the final `HirModule.
   symbols` MIR consumes still diverged — meaning the real defect is
   upstream of `SymbolTable.define()`'s dedup logic: either (a) a
   surface/import "prescan" pass and the "real" HIR-lowering pass are
   separate `HirLowering`/`SymbolTable` instances, and the real pass
   independently re-derives its own numbering from scratch, discarding
   whatever my instrumentation observed on the (possibly throwaway)
   instance; or (b) `HirModule.symbols` is captured (in the `HirModule(...)`
   constructor — two call sites in `module_lowering.spl`, an early
   bootstrap-mode return around line 2247 and the normal-path construction
   around line 2375) at a point that PRECEDES a later, repeat invocation of
   `register_imported_type_methods` whose id-minting still lands in the
   live object. Distinguishing (a) from (b) needs tracing exact call
   ordering against `HirModule` construction, which this session did not
   have remaining budget to complete.

**Root question still open**: WHY does `register_imported_type_methods` run
more than once for the same imported type? `register_imported_symbol`'s
composite branch calls it unconditionally regardless of `already_bound`
(the guard only gates the `rename_symbol`/`bind_qualified_type` calls, not
the `register_imported_type_methods` call) — by design, per the comment at
`module_lowering.spl:786-791` about directory-sibling ENUM prebinding
needing methods registered "on both paths". Whether an analogous
directory-sibling prebinding path exists for CLASSES, and whether its
idempotency assumption is what actually breaks under this repro's plain
`use fh_mod.FileHandle` 2-module shape (no directory-sibling relationship at
all in this minimal repro — worth checking whether that mechanism fires
even so, or whether a THIRD, distinct trigger is responsible), is the
concrete next thing to check.

**Fast repro** (cross-module, no traits, seconds not 18 minutes — use a
source directory with NO hyphens in its path to avoid the unrelated
`_hir_symbol_owner_module`/`hir_module_logical_name_from_path` sanitization
mismatch, which independently produces a DIFFERENT failure — an undefined-
symbol LINK error rather than "unresolved method call"):
```
# fh_mod.spl
class FileHandle:
    fd: i64
    static fn open(path: text) -> Result<FileHandle, text>:
        Ok(FileHandle(fd: 1))
    fn write_text(s: text) -> Result<i64, text>:
        Ok(0)
    fn close() -> Result<i64, text>:
        Ok(0)

# main.spl
use fh_mod.FileHandle

fn main() -> i64:
    val h = match FileHandle.open("x"):
        case Ok(hh): hh
        case Err(e): return 1
    match h.write_text("hi"):
        case Ok(_): pass
        case Err(e): return 1
    match h.close():
        case Ok(_): pass
        case Err(e): return 1
    print("ok")
    return 0
```

**AOT `rt_io_file_*` stub verdict: still UNDETERMINED.** This session did not
re-run the full 18-minute `rt_io_file_roundtrip` closure — the fast repro
above still fails identically to the full closure's own failure signature,
so a full-closure run would only reconfirm the same still-open blocker at
much higher cost with no new information.

### Next steps (supersedes the 6th layer's "bisect the full closure" note —
the failure IS already isolated to the fast repro above, no further
bisection needed; what remains is the id-divergence root cause, not scale)

1. Determine whether HIR lowering runs a separate, discarded "prescan"
   `HirLowering`/`SymbolTable` instance distinct from the one whose state
   becomes `HirModule.symbols` — or whether `HirModule.symbols` is captured
   before a later repeat `register_imported_type_methods` invocation lands.
2. Find and eliminate (or correctly guard) the repeat invocation of
   `register_imported_type_methods` for the same imported type within one
   module's lowering — check whether the directory-sibling-prebinding path
   documented for enums (`module_lowering.spl:786-791`) also applies to
   classes and is what's firing here.
3. Once the true duplicate-invocation source is fixed at its root, re-run
   the fast repro above, then the full 18-minute `rt_io_file_roundtrip`
   closure, to finally get the `rt_io_file_*` AOT stub/no-stub verdict.

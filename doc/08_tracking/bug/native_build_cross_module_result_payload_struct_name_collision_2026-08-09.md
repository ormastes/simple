# `native-build` MIR lowering: cross-module `Result<T, E>` payload struct-name recovery collides/misses across modules — 4th layer, RESOLVED 2026-08-09 (5th layer surfaced)

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

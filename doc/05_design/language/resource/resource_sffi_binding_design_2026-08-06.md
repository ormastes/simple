# Design: `resource` SFFI Binding — Grammar, Inference, Lowering

**Date:** 2026-08-06
**Status:** Proposed (Phase 1 detail)
**Architecture:** `doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`

## 1. Grammar A — attribute form (Phase 1, implement first)

Existing raw declarations stay valid and become the private SFFI layer:

```simple
extern fn rt_file_open(path: text) -> i64
extern fn rt_file_read(handle: i64, buffer: mut [u8]) -> i64
extern fn rt_file_close(handle: i64) -> bool

@sffi(prefix: "rt_file", invalid: -1)
resource File
```

Derived public API (generated adapters; raw `rt_*` not exported as app API):

```simple
File.open(path) -> File?          # acquire family; invalid sentinel -> nil
file.read(buffer) -> i64          # method: borrows receiver
file.close()                      # consuming; sugar for drop(move file)
# hidden drop hook calls rt_file_close exactly once
```

`@sffi` is parsed by the **compiler frontend** (`parse_attributes()`,
`parser_extensions.spl:20-38`) — not sffi_gen's private text parser. sffi_gen
reads the same attribute off the real AST; its `@Lib` text parser
(`sffi_gen/parser.spl:106-115`) is unchanged for legacy specs.

### `@sffi` schema

```
@sffi(
    prefix: "rt_image",       # required: extern family root
    handle: i64,              # default i64
    invalid: 0,               # default 0 (image_sffi's `>0` shows this varies — always explicit in stdlib)
    retain: rt_image_ref,     # optional
    release: rt_image_unref,  # optional (else inferred; fail-closed)
    sharing: auto,            # auto | none | wrapper | foreign
    thread_safe: false,       # gates @R
)
resource Image
```

Add `sffi` + `resource_*` names to the known-attribute lint list
(`90.tools/fix/rules/impl_/lint_annotation.spl:14-23`).

## 2. Grammar B — sugar (Phase 2)

```simple
resource File from rt_file:
    invalid: -1

resource Image from rt_image:
    retain: rt_image_ref
    release: rt_image_unref
    sharing: foreign
    thread_safe: true
```

Pure desugar to Grammar A in the frontend. No separate semantics.

## 3. Grammar C — explicit escape hatch (Phase 3)

For APIs conventions can't classify:

```simple
@handle(type: i64, invalid: 0)
resource Image

@resource_acquire(Image)
extern fn strange_make_picture(path: text) -> i64

@resource_method(Image, receiver: 1, access: exclusive)
extern fn library_decode(data: [u8], image: i64) -> bool

@resource_retain(Image)
extern fn increment_picture_usage(image: i64)

@resource_release(Image)
extern fn abandon_picture(image: i64)

@resource_borrow(Device, from: context)
extern fn rt_context_get_device(context: i64) -> i64
```

Later typed-SFFI surface (same ABI, `Image` lowers to configured raw repr):

```simple
extern fn image_load(path: text) -> Image?
extern fn image_width(image: Image) -> i64        # borrowed for call
@consumes(image)
extern fn image_release(image: Image)
```

## 4. Convention inference — fail-closed, family-scoped

Inference operates **only** inside a declared family (`prefix:`). Never a
global `rt_*` scan.

| Family | Names | Contract |
|--------|-------|----------|
| Acquire | `open, create, new, alloc, acquire, copy, clone` | returns new owned `R` |
| Release | `close, destroy, free, release, unref, dispose` | consumes one claim |
| Retain | `retain, ref, add_ref` | +1 foreign strong ref |
| Validity | `is_valid, valid` | raw-handle validity test |
| Methods | remaining fns with one unambiguous handle param | prefix stripped, exposed as method |

Example mapping: `rt_file_open → File.open`, `rt_file_read → file.read`,
`rt_file_close → drop hook + consuming file.close`,
`rt_file_available → File.available` (no handle param → static).

**Fail-closed rules (compile errors, not guesses):**
- Ambiguous/duplicate destructor → error.
- Multiple candidate receiver params → require `receiver:`.
- Function returning another handle type → require owned/borrowed metadata
  unless a strict acquire family matches.
- No recognized release fn → do NOT silently create an owning resource;
  require `release:` or `sharing: none`.
- Explicit metadata always overrides names.

## 5. Borrowed resources

A handle owned by another resource must not become an independent owner.
Method rule: a borrowed resource returned by a method is tied to the receiver
unless configured otherwise. Free functions declare `from:`; statics declare
`static: true`:

```simple
@resource_borrow(Device, from: registry)
extern fn rt_registry_device(registry: i64, id: i64) -> i64

@resource_borrow(Device, static: true)
extern fn rt_default_device() -> i64
```

Public wrapper uses the ordinary borrow type: `fn Context.device() -> borrowed
Device` — no `ForeignBorrow<T>`. Name-based borrow suggestion (`get`,
`current`) is allowed only as a *prompt* in lenient mode; robust mode requires
explicit metadata — this distinction is safety-critical.

## 6. Lowering

**Unique R:** `{ raw_handle }` + static drop metadata. Drop edges emitted in
MIR on scope exit, early return, and `?` propagation (reuse the parsed-but-
unused `defer`/`errdefer` lowering path where it fits). `close()` = consuming
drop; the value's ownership state → Dropped; later use is a `55.borrow` error
(needs the remaining half of G1: forward propagation of moves is already
fixed — `moved_now` at `borrow_graph.spl:459`, SF1 2026-07-28. Move-site
emission is partially closed as of 2026-08-07: `MirBuilder.emit_move`
originally had exactly one caller in the whole compiler
(`mir_lowering_stmts.spl:743`); call-argument use-detection and
move-emission both landed (`55.borrow/borrow_check/mod.spl` `case Call` arm;
`50.mir/_MirLoweringExpr/switch_operators_calls.spl` `case
HirTypeKind.Isolated(_):`), giving `emit_move` a second caller. Resource move
sites still missing: return, reassignment, field store, collection store
(`arr[i]=`/`d[k]=` via `rt_array_set`/`rt_dict_set`, `.push()` via
`rt_array_push`) — tracked in
`doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`).
The upstream parser gap is RESOLVED: `iso`/`mut` now parse in parameter
position (`10.frontend/core/parser.spl:506-534`, "LANE ISO2", 2026-08-07;
original bug `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`).

**Wrapper RC (`*R`):** control block `{strong, weak, raw_handle, release_fn}`
allocated on first share; existing `rc_box_init` runtime machinery is the
starting point. `@R` = atomic ops on the same block; gated on `thread_safe`.

**Foreign RC:** copy → `retain:` call; drop → `release:` call; no control
block.

**Borrow pinning (SafeHandle rule):** for the duration of any extern call
taking a borrowed `R`, the owner cannot be dropped/moved — enforced
statically by the borrow region covering the call, including blocking calls.

**`raw<T>` escape:** extracting the raw handle is legal only in generated SFFI
modules or an explicit unsafe boundary; elsewhere it is a compile error.

## 7. Interpreter/JIT parity

`bin/simple test` (tree-walk) and `bin/simple run` (Cranelift JIT) are
different engines; both must implement drop timing identically. Every spec in
the test plan runs under `SIMPLE_EXECUTION_MODE=interpreter` and `jit`.
Native codegen dict pitfalls (`.claude/rules/code-style.md`) apply to any
resource-registry tables: no `Dict.len()`, no `.get()` on struct-valued dicts.

## 8. Migration

- Pilot: `image_sffi.spl` (`ImageData` class → `resource Image`) and a `File`
  family — the two exemplars in the research doc.
- The library `Resource` trait (close/is_open/resource_name) is subsumed;
  deprecate after pilots land.
- `ffi/` vs `sffi/` duplicate trees: bind only against `sffi/`; twins are
  pre-existing cleanup debt (tracked in plan WP-0).
- No bulk rewrite: existing raw wrappers keep working; families convert
  one-by-one, each with specs.

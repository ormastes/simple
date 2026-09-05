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

## Appendix A — Selection-rule verification + census (2026-08-07)

**Status check first:** as of this appendix, `resource`/`@sffi` are not
parsed by the real frontend at all — repo-wide grep for
`parse_resource_decl`/`DECL_RESOURCE`/`@sffi` (as consumed attribute) in
`src/compiler/` returns zero hits; this is WP-A of
`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`,
not yet landed (confirmed also absent from every live sibling session's
uncommitted tree at check time). See
`doc/08_tracking/bug/resource_decl_and_sffi_attribute_not_parsed_2026-08-07.md`.
Everything below is therefore validated against the design **on paper** and
against a real, currently-RED pilot spec — not against a working compiler.

### A.1 Selection-rule verdict: tier does not select strategy; it constrains availability

The task's working hypothesis — "runtime family / lib tier of the defining
module picks unique-vs-shared" — is **not** what the design specifies, and
the doc set already disproves it directly:

- §3 here: RC "activates only when the program writes `*R`/`@R`" — the
  *use-site sigil* selects sharing, not the declaration's tier.
  `sharing: auto` (§4 of the schema table above) picks foreign-vs-wrapper RC
  from **retain/release pair presence**, a per-resource `@sffi` metadata
  fact, not a tier fact.
- Architecture doc §7: `@R` is gated on the resource's own declared
  `thread_safe:` flag, again per-resource metadata, not tier.
- Architecture doc §3: unique `R` is explicitly "the right default for
  files, sockets, command buffers, transactions, locks" regardless of which
  tier declares them — `nogc_sync_mut/io/file.spl` and
  `gc_async_mut/atomic.spl` both default to unique ownership unless the
  program writes `*R`.

**Adopted rule:** ownership strategy (unique / wrapper-RC / foreign-RC) is
selected by **per-resource `@sffi` metadata** (`sharing:`, presence of
`retain:`/`release:`, `thread_safe:`) plus **the sigil written at each use
site** (`R` vs `*R` vs `@R`). Tier is not a selection input.

**Refinement that *is* tier-dependent (constrains, not selects):** tier
bounds which strategies are *legal*, because `sharing: wrapper` allocates a
Simple-side control block (`{strong, weak, raw_handle, release_fn}`, §6
above) and `nogc_async_mut_noalloc` forbids allocation by contract
(`doc/05_design/lib/runtime/noalloc_stdlib_design.md`). Evidence: a
repo-wide scan for `_free`/`_close`/`_destroy`/`_release`/`_unref`/`_dispose`
extern declarations under `src/lib/nogc_async_mut_noalloc/**` returns **zero
matches** — the noalloc tier currently declares no foreign resource handles
at all, consistent with (not proof of) the constraint. Under this rule, in
`nogc_async_mut_noalloc` only unique `R` (`sharing: none`, no allocation) or
`sharing: foreign` (retain/release calls, no control block, per §6 "Foreign
RC: ... no control block") would be legal; `sharing: wrapper` would not be,
until/unless a noalloc-safe control-block allocator exists. This is a
constraint to enforce later in WP-A/WP-C, not evidence against the adopted
rule.

### A.2 Census (owned code only; vendor paths excluded per task scope)

Method: `grep -rEon "extern fn (rt_[a-z0-9_]+)_(free|close|destroy|release|unref|dispose)\("`
over `src/lib/**` and `src/app/**` (`.spl` only), excluding
`src/lib/nogc_sync_mut/ffi/` (the `sffi/` twin is canonical — see research
doc §3.1) and the parallel `src/app/io/*_ffi.spl` twins of `*_sffi.spl`, and
filtering 3 false positives (`rt_glfw_should_close`,
`rt_sdl2_window_should_close`, `rt_sdl_window_should_close` — status queries,
not release calls; matched only because the name ends in `_close`).

**Total: 85 distinct release-family externs** (88 raw matches − 3 false
positives), spanning acquire verbs (`_open`/`_load`/`_create`/`_alloc`/
`_new`) paired 1:1 with a release verb per family, plus a handful with a real
`retain`/`release` pair (foreign-RC candidates: `rt_cuda_primary_ctx_retain`/
`_release` in `src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:21-22`).

**Per-tier split (declaration sites, not deduplicated families — a family
can appear once per tier that reimplements it):**

| Tier | Declaration sites |
|------|-------------------|
| `nogc_sync_mut` | 100 |
| `app/io` (application layer, not a stdlib tier) | 21 |
| `nogc_async_mut` | 12 |
| `gc_async_mut` | 7 |
| `common` | 4 (baseline debt — pure tier should not declare impure externs, matches the 14-file baseline in `doc/04_architecture/lib/host_io_layering/three_tier_lib.md`) |
| `app/ui.chromium`, `app/ui.web`, `app/simple_process_manager`, `app/ffi_gen.specs`, `app/debug` | 1 each |
| `nogc_async_mut_noalloc` | **0** — supports §A.1's constraint finding |

Representative families (acquire → release, tier, defining module):

| Family | Acquire | Release | Tier | Module |
|--------|---------|---------|------|--------|
| File | `rt_io_file_open` | `rt_io_file_close` | nogc_sync_mut | `io/file.spl` |
| Image | `rt_image_load` | `rt_image_free` | nogc_sync_mut | `io/image_sffi.spl` (existing design-doc exemplar) |
| CudaPrimaryContext | `rt_cuda_primary_ctx_retain` | `rt_cuda_primary_ctx_release` | nogc_sync_mut | `gpu/engine2d/cuda_session.spl` (real retain/release pair) |
| CudaContext | `rt_cuda_ctx_create` | `rt_cuda_ctx_destroy` | gc_async_mut, nogc_sync_mut (dup) | `cuda/ffi.spl` |
| HttpClient | (impl.) | `rt_http_client_destroy` | nogc_sync_mut, app/io (dup) | `io/http_sffi.spl` |
| Sqlite | (impl.) | `rt_sqlite_close` | nogc_sync_mut, app/io (dup) | `io/sqlite_sffi.spl` |
| AtomicCounter | (impl.) | `rt_atomic_int_free` | gc_async_mut, nogc_sync_mut (dup) | `atomic.spl` |
| TorchTensor | (impl.) | `rt_torch_torchtensor_free` | nogc_sync_mut, common (dup) | `torch/sffi.spl` |
| Rapier2dWorld/Body/Collider/Joint/Contacts (5 families) | (impl.) | `rt_rapier2d_*_free` | nogc_sync_mut, app/io (dup) | `io/rapier2d_sffi.spl` |
| LyonPath/PathBuilder/Transform/VertexBuffer/IndexBuffer/FillTessellation/StrokeTessellation (7 families) | (impl.) | `rt_lyon_*_free`/`_close` | nogc_sync_mut, app/io (dup) | `io/graphics2d_sffi.spl` |

### A.3 Pilot migration (2026-08-07)

Per §8 above ("No bulk rewrite... families convert one-by-one"), 4 of the 85
families were selected for the pilot, chosen for ownership-strategy and tier
diversity: **File**, **Image** (unique `R`, `nogc_sync_mut`, `sharing:
none`), **CudaPrimaryContext** (`sharing: foreign`, `nogc_sync_mut`, the one
family in the census with a genuine retain/release pair), **AtomicCounter**
(`sharing: wrapper`, `gc_async_mut`, tests that wrapper-RC allocation is
legal in an allocating tier).

Because WP-A has not landed (§ above), the pilot could not migrate callers
to a working `resource` surface — there is nothing yet to migrate them to.
Per the task's own stated fallback ("if the compiler cannot yet reject them,
leave the spec RED and file a `doc/08_tracking/bug/` record"), the pilot
instead wrote the **intended** Grammar-A source
(`@sffi(prefix: "rt_io_file", invalid: -1) resource File`, etc.) as real
module-level declarations in
`test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` and ran it
through the real frontend via `bin/simple test`. It fails to parse
(`Unexpected token: expected Fn, found Identifier { name: "resource", ... }`,
`Results: 1 total, 0 passed, 1 failed`, exit 1) — left RED intentionally, not
weakened to test a hand-rolled `class X { handle: i64 }` workaround (which
would just reproduce the exact boilerplate `resource` exists to delete — see
§3.1 image_sffi exemplar). Bug doc with unblock condition:
`doc/08_tracking/bug/resource_decl_and_sffi_attribute_not_parsed_2026-08-07.md`.
No existing callers were touched — there is no working target to migrate
them to yet.

# Typed Facet Witness Transaction — TLDR

**Status:** proposed prerequisite; `facet<T>` is not implemented.

- Never cast aspect-pack payload bytes to a typed facet. A facet is an opaque
  `FacetRef<T>` over a rooted receiver, loader-owned immutable vtable, optional
  sidecar, exact binding ID, generation, and pin.
- Use SHA-256 over one canonical binary identity grammar and distinct opaque
  four-`u64` concrete/interface/method/implementation/binding types through SHB,
  HIR/MIR, pack, and runtime. Text keys remain compatibility-only.
- Root catalog authority in an application signature or independently pinned
  digest, then intersect it with an immutable out-of-band minimum trust policy;
  catalog/route fields can strengthen but never downgrade it.
- Add one content-hash-bound `.facet_witness` section to ordinary facet SMFs.
  It names exact IDs, ABI/layout hashes, `STATELESS`/`PER_BINDING`/`PER_OBJECT`
  scope, and authenticated factory/destroy/method callable ABI records. The
  loader, not the module, builds the exact-layout read-only vtable.
- `ModuleLoader` owns one prepare -> map -> relocate -> seal -> validate ->
  factory -> atomic publish transaction. One immutable admission lease moves
  into the single authoritative loader record; there is no second typed commit.
  Any failure destroys staged sidecars, removes staged symbols, unmaps staged
  memory, releases the admission lease, and advances no generation.
- `try_facet<T>` is resident-only and performs no I/O, parse, hash, decompress,
  scan, map, or name lookup. `facet<T>`/`require_facet<T>` may load only when an
  explicit execution-context loader capability and policy permit it.
- Per-object instances use their own object/binding/generation single-flight and
  rollback; a resident no-I/O factory runs once for each distinct object under
  an unload-counted exact-generation activation guard.
- Unload first quiesces acquisition, waits for exact-generation public pins and
  activation/invocation guards, destroys
  sidecars while code is mapped, removes witness/symbol visibility, then unmaps.
  Cleanup failure quarantines the non-reusable generation.
- Frontend adds dedicated AST/HIR facet-acquisition variants; type checking
  resolves one sealed facet interface and exact result types. HIR
  `MethodResolution.FacetMethod` carries the slot and all identities into MIR;
  `MirFacetCallAbiV1` survives as `CallIndirectAbi`, never `rt_vtable_lookup` or
  metadata-free `CallIndirect`.
- `FacetImplAbiHashV1` canonically binds implementation/state/access/layout,
  factory/destroy signatures, and the ordered method/callable ABI set.
- Hard blockers include authenticated Catalog V3/ModuleEntry V4 fields,
  transactional mapping/publication, runtime concrete descriptors, explicit
  loader context, real single-flight, sidecar identity/rooting, and native
  x86_64 indirect-call support.

Full contract:
`doc/04_architecture/compiler/aspect_dynload/typed_facet_witness_transaction_2026-08-26.md`

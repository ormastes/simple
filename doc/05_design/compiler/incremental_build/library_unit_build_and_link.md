# Library Unit Build and Link

**Status:** design + first slice (plan/key pure functions, no wiring). 2026-11-13.
**User request:** "each lib build than link to binaries (not yet done)".

Today `native-build` compiles an entry's whole closure as ONE program: one
HIR/MIR pipeline over all ~1650–3134 modules, one object per module, one link.
There is no target model (`lib_only_build_feasibility_2026-08-09.md` §0.1),
`simple.sdn dependencies:` is traversed by no build path (§0.2), and the
`interface_digest_of` machinery (`cache/action_key.spl:184`) is computed by
SIF/SMF but drives no reuse decision. This design builds each **library unit**
once into a reusable archive + interface artifact and links binaries from them.

## 1. Unit model (from `simple.sdn`)

A **unit** is one `simple.sdn` whose `project:` block has `type: library` or
`type: runtime`. `type: application` manifests are **link targets** (they own
an entry and consume units, they are never archived); `type: metadata` is
ignored. Units are named by `project.name`; their source set is
`root`/`source_dir` relative to the manifest directory. Edges come from
`project.dependencies[].project`, a path relative to the manifest directory,
normalised as pure text (no filesystem) to a repo-relative directory and then
matched against the other manifests' directories.

Measured drift (2026-11-13), which the planner must **fail closed** on, not
normalise away: `src/lib/simple.sdn` depends on `../../compiler_rust` (resolves
to `compiler_rust`, no manifest there — the manifest is at
`src/compiler_rust`), and `src/app`/`src/compiler` depend on `../../rust`,
which does not exist at all. An unresolvable edge makes the plan `Err`; fixing
those four lines is a prerequisite for turning the flag on, not something the
planner guesses. Measured 2026-11-13 with `library_unit_decl_parse_v1` over all seven
real manifests (the `src/lib` one parses, giant `mc_exceptions:` string included):
`plan-error unit 'simple-app' depends on 'rust' but no manifest declares a unit there`.

Current units/targets: `simple-std` (src/lib, library), `simple-compiler-common`
(src/compiler/00.common, library → ../../lib), `simple.runtime` (src/runtime,
library), `simple-rust-runtime` (src/compiler_rust, runtime), `simple-compiler`
(src/compiler, application → lib), `simple-app` (src/app, application →
compiler, lib). The compiler proper becomes a library unit by changing its
`type` once the Stage 3 binary is expressed as a link target (§6).

## 2. Interface artifact — what a dependency leaks into a unit's objects

MIR lowering of a module reads far more than its importers' `fn` headers
(`mir_shard_export_summaries.md` rows 1-22): struct/class field order and
types, layout digests, enum discriminants and payload shapes, callee signatures
AND parameter defaults, methods/extensions, trait implementors and vtable
shapes, imported globals/constants and externs (rows 2-19). So the per-module
digest is **`native_interface_whole_digest_v1`** over the body-free declaration
carrier (`cache/native_interface_slice.spl`: every declaration keeps its header
and nested non-body lines — fields, variants, signatures with defaults — and
drops only bodies). It is explicitly NOT `interface_digest_of_source`, whose
`source_interface_parts` heuristic keeps only header lines and misses a field
change. Per unit: `interface_digest_of(["simple/library-unit-iface/v1",
"<module>:<module digest>", …])`, stored as `iface.sdn`
(`library_unit_iface_v1.spl`, decode fails closed on format/digest mismatch).
A body-only edit inside a unit leaves every dependent's key intact.

Two rows are NOT covered by any interface digest and are handled separately:

- **Row 20, generic monomorphization.** `40.mono` inserts each specialization
  into its *template owner's* HIR, so a dependency's objects would otherwise
  vary with its users' instantiations. Rule: a unit archive contains only
  instances whose template AND arguments are both inside the unit. Cross-unit
  instances are produced by the existing generic-instance pre-link lane
  (`generic_instance_prelink_v1.md`: `needed = ∪ generic-spec(all modules)`,
  key `generic_instance_body_key_v1(concrete_key, template body digest) +
  producer`, COMDAT/linkonce_odr) and added to the link set beside the
  archives. Their key already includes the template owner's **body** digest,
  which is correct — an instance body is the dependency's body.
- **Row 22, order-dependent counters** (`canonical_type_symbols`,
  `mcdc_next_runtime_id`): values depend on lowering order across the whole
  closure. Separate compilation needs them unit-deterministic (derived from
  symbol identity, not visit order) or recorded in the receipt and rejected on
  mismatch. **Blocker for slice 5; not solved by any digest.** Rows 12/14
  (process-global tables) are per build process and so per unit build.

## 3. Archive layout and cache key

Objects land under the existing lane scope, never a new tree:

```
build/bootstrap/native_cache/<lane>/<scope_key>/units/<unit-name>/<unit_key>/
    objects/<module>.o      lib<unit>.a (thin archive over objects/)
    iface.sdn               unit interface digest + per-module digests
    receipt.sdn             producer identity, source digest, dep keys, verdict
```

`unit_key = sha256("simple/library-unit/v1" ; frame(producer_identity) ;
frame(unit_source_digest) ; frame(dep_1 iface) ; … )` with dependencies sorted
by name and every component length-framed by `cache_key_frame`
(`incremental.spl:626`) so `("ab","c")` and `("a","bc")` never collide.
`producer_identity` is the existing `native_build_producer_identity` (exe,
compiler, runtime, bundle, ABI); `unit_source_digest` is `library_unit_source_digest_v1`: sha256 over the
unit's sorted, length-framed `(path, sha256(source))` pairs. Dependencies enter only through their
**interface** digest, so a dependency's body change does not rebuild its users.

## 4. Dependency-ordered parallel scheduling

Planning is a pure function (`library_unit_plan_v1`): parse manifests → units →
Kahn order with explicit cycle detection returning `Err` naming the cycle
(`BuildGraph.topological_order` is DFS-with-visited and silently tolerates
cycles, which is why it is not reused for planning). Each unit gets a `level`
(longest path from a root); all units at one level are independent and run
concurrently. Execution reuses `ParallelBuilder`/`BuildGraph` (`parallel.spl`)
with one `BuildUnit` per library unit and the existing process pool
(`native_codegen_pool_v1`, per-file workers) **inside** each unit. Ownership is
by immutable receipt (`receipt.sdn` written once under the final `unit_key`,
same pattern as `native_file_worker_owner_claims_v1`); a second lane finding a
complete receipt reuses it. No new locks — the repo is lockless by default.

## 5. Link

A link target resolves its unit closure, requires every unit's `receipt.sdn`
verdict `ok`, and links the entry's own objects plus the archives in reverse
topological order (`lib<leaf>.a` last). The link step is the existing
`native_link_receipt_v1` path with an archive list instead of a flat object
list; the link receipt records each `unit_key` so a relink is skipped when the
set is unchanged.

**Go-to-end** (`go_to_end.spl`): a unit with any failed module produces **no**
archive; its receipt verdict is `failed` with the per-module manifest, every
dependent unit is poisoned transitively, and link never runs — same "no partial
binary" rule, now at unit granularity, so one broken leaf no longer blocks
building the independent units.

**Per-file route (#8504):** the per-file lane's unit MIR ownership gate applies
*within* a library unit — file units nest inside it and the unit's archive is
only sealed when the gate admits all of its files. Cross-unit MIR reads go
through the dependency's sealed interface, never its shards.

## 6. Adoption behind a flag

`SIMPLE_NATIVE_LIBRARY_UNITS=1` (and `native-build --library-units`) switches
the driver from whole-closure to plan → build units → link; unset keeps today's
path byte-for-byte. Stage 3 adopts first (`simple-std`, `simple.runtime`, then
the compiler as a unit); the bootstrap script's **Stage 4** full-CLI relink
reuses the Stage 3 unit archives and only builds the CLI-only units, which is
the user-visible win. Receipt-gate and per-lane cache scope rules are unchanged.

## 7. Slices

1. (this change) `library_unit_plan_v1.spl`: manifest → ordered, levelled unit
   plan with cycle detection and fail-closed dependency resolution;
   `library_unit_cache_key_v1`. Specs red→green, no wiring.
2. (done) `library_unit_iface_v1.spl`: unit source digest over the real file
   set; body-free per-module digests; `iface.sdn` writer/reader.
3. Archive writer (thin `.a` over the existing per-module objects) + receipt.
4. `BuildGraph` adapter: plan → `BuildUnit`s, poison propagation.
5. Link from archives; Stage 3 behind the flag; Stage 4 reuse; manifest drift fix.

# A swapped duplicate-`type` alias winner is INERT — the alias target is never stored

- **Filed:** 2026-08-01
- **Status:** OPEN (latent). No miscompile today; becomes a live miscompile the
  moment aliases are made transparent.
- **Severity:** LOW today / **BLOCKER for the alias-transparency work**
- **Area:** `src/compiler/20.hir` name resolution
- **Relates to:** `glob_ungate_swaps_import_winners_2026-08-01.md` (356 swaps /
  164 names, 323 of them last-wins), `f7bfaf973de` (TAL2)

## Summary

`SymbolKind.TypeAlias` is last-write-wins in `SymbolTable.define`, so when two
reachable modules provide the same alias name the traversal order decides the
winner. That is real. **But for `TypeAlias` specifically the swap cannot change
any lowered type, because the alias TARGET is never recorded anywhere.** Two
providers of the same alias name are indistinguishable to every downstream
consumer, so a swapped alias winner changes a symbol id and nothing else.

This closes the `TypeAlias` slice of the 323 last-wins swaps. It says nothing
about the `Function` / `Const` slice, which does carry a real type
(`declared_surface_callable_type`) and is NOT covered by this argument.

**Update 2026-08-01 — the `Function` / `Const` slice is now also closed**, by a
different argument, in `glob_ungate_swaps_import_winners_2026-08-01.md`. Short
version: `declared_surface_callable_type` returns `nil` under
`registering_import_symbols`, so an imported `Function` stores no type either;
`defining_module` is the only field that differs between two candidates and has
zero Function/Const readers; and MIR emits calls by NAME STRING
(`symbol_display_name` -> `sym.name` = the shared `local_name`), not by symbol
id. Inert on interpreter, JIT and native. The one exception is the
entry-closure bootstrap lane, where `qualify_imported_function_symbol` renames
the winner to `{module}.{name}` and the swap therefore IS observable.

## Evidence (PROVED, `/usr/bin/grep` pinned, at tree 109,542)

1. **Exactly two sites create a `TypeAlias` symbol, and both store `nil` for the
   symbol's type:**

       module_lowering.spl:632   name=local_name kind=SymbolKind.TypeAlias TYPE_ARG=nil
       module_lowering.spl:1855  name=name       kind=SymbolKind.TypeAlias TYPE_ARG=nil

   (632 = imported alias; 1855 = a module's own alias, added by TAL2.)

2. **Nothing in `src/compiler/` ever reads `SymbolKind.TypeAlias` back.** A grep
   for the constant across `src/compiler/` minus the two `define` calls returns
   zero lines. The only reader in the whole tree is
   `src/app/interpreter/collections/persistent_symbol_table.spl:283`, which maps
   it to the display string `"type"` — a different symbol table, in a tree with
   no external importers.

3. **`lower_named_kind` never expands an alias.** `hir_lowering/types.spl:554`
   resolves a named type with `self.symbols.lookup_or_invalid(name)` and builds
   `HirTypeKind.Named(symbol_id, hir_args)`. There is no alias-expansion branch.

4. **No name-keyed alias-target registry is consulted.** Every `type_aliases`
   reference in `src/compiler/20.hir/` is a `.keys()` / `.contains_key(name)`
   NAME operation; the alias VALUE is read at exactly one place,
   `module_surface.spl:262`, purely to copy it into the surface struct, where
   nothing consumes it. `src/compiler/30.types/` references `type_aliases`
   **0** times.

Corollary of 3 + 4: a parameter annotated `Bytes` where `type Bytes = List<u8>`
does NOT lower to a list — it lowers to an opaque `Named`. Aliases are not
transparent anywhere in HIR or the type layer.

## Census (module-level `type X =` only, column 0)

Counting any-indent `type X =` inflates the census by ~17%: trait associated
types and doc-comment examples match too. `Item` looks like a 27-site duplicate
that way and is in fact **not a module-level alias at all**.

| metric | any-indent | module-level (correct) |
|---|---|---|
| alias declaration sites | 388 | **333** |
| distinct alias names | 190 | **185** |
| names declared in >1 file | 63 | **52** |

### All three injection routes, enumerated

A duplicate can only bite if two providers of one name reach **one module's**
symbol table. There are exactly three routes, and all three are empty at the
tip this was measured on:

| route | result |
|---|---|
| a file declares alias `N` **and** named-imports `N` | **0** |
| ≥2 glob-imported modules provide the same alias name | 13 (file, name) pairs; of these 6 involve a divergent-target name |
| — of those 6, surviving hand-verification | **0** |

The 6 divergent-target candidates were all `Count`, and every one dissolves on
inspection: `failsafe/mod.spl` and the `mcp/core/*` files glob providers that
**all** declare `type Count = i64`, and `sdoctest/mod.spl` globs siblings that
declare no `Count` at all — that row is an artifact of joining on module
basename (`sdoctest/discovery` vs `tooling/testing/discovery`). The only `i32`
providers of `Count` live under `src/compiler_rust/lib/std/src/tooling/**`,
which none of those roots reach. A basename join is unavoidable here because
path-derived module names carry numbered-layer segments
(`compiler.30.types.foo`) while `use` lines use the symlink spelling
(`compiler.types.foo`) — a full-path join silently yields zero.

Of the 52 duplicated names, **40 have providers that all agree on the target**
(a swapped winner is harmless even under a future transparent-alias
implementation). **12 have divergent targets** — the set that would become live:

| name | divergent targets |
|---|---|
| `Symbol` | `HirSymbol` vs `text` |
| `Bytes` | `i64` vs `List<u8>` |
| `Count` | `i32` vs `i64` |
| `LineNumber` | `i32` vs `i64` |
| `Seconds` | `f64` vs `i32` |
| `Vec2d` / `Vec4d` | `Array<f64,N>` vs `FixedVec<f64>` |
| `Vector2` / `Vector3` / `Quaternion` / `Matrix3` / `Matrix4` | same underlying type via different module spellings (cosmetic) |

Genuinely divergent underlying type: **7 names** (`Symbol`, `Bytes`, `Count`,
`LineNumber`, `Seconds`, `Vec2d`, `Vec4d`).

## `Symbol` is not a duplicate-alias conflict

`Symbol` has 33 module-level declarations (32 × `= text`, 1 × `= HirSymbol`) and
was the name this lane was opened on. It cannot be a duplicate conflict: the HIR
symbol table is **per module** — `begin_module` reassigns `self.symbols` from a
fresh table (`hir_lowering/types.spl:207`), and all three lowering call sites in
`driver_hir_pipeline_lowering.spl` construct a fresh `HirLowering` per source. A
direct-glob exposure scan finds **zero** modules receiving `Symbol` from two
providers. The 315 `unresolved type: Symbol` errors seen at `f7bfaf973de` were
an unrelated population — files under `src/compiler/driver/` that contain
neither the token `Symbol` nor any `use` line, all reporting an identical
error signature alongside `HirType` / `MirSignature` / `Span` — i.e. the
import-surface layer, not aliases.

## The thing that actually needs fixing, and its ordering constraint

Aliases should be transparent. **Whoever implements that MUST make `TypeAlias`
first-write-wins in `SymbolTable.define` in the same change**, or the 7
divergent-target names above turn from inert into live miscompiles the instant
the target starts being consulted. Today the last-wins ordering is invisible
precisely because the target is discarded; transparency removes that shield.

## Probe matrix (stage2 self-hosted, bare positional `native-build`)

Seven shapes covering every outcome a duplicate alias could have — error, wrong
pick, no pick, order dependence — plus controls:

| case | shape | unresolved |
|---|---|---|
| `a` | same alias name, 2 modules, **different targets**, both used | none |
| `s1` / `s2` | nominal `struct` vs same-named alias, **both load orders** | none |
| `g` / `gs` | glob-injected private alias vs named-imported struct, both orders | none |
| `own` | module's own alias shadowing a named-imported struct | none |
| `fwd` | alias used **before** its `type` line (the `Node::Let` ordering analogue) | none |
| `hello` | positive control, `fn main(): print(1)` | none |
| `n` | negative control, undefined type | **`unresolved type: NoSuchTypeHere`** |

`fwd` passing shows aliases do **not** share the module-level `val`/`var`
ordering weakness: TAL2 registers from `module.type_aliases` in pass 1, which is
order-independent.

Harness note: every case including `hello` ends with `bootstrap entry lowered to
0 MIR instructions (ret-0 stub module)`. That is a property of the single-file
bare-positional lane, identical for a trivially correct program, so it is not a
signal — the discriminating signal is the `unresolved` class, and the negative
control confirms the gate still fires.

## Not claimed

- Nothing *here* covers the `Function` / `Const` half of the 323 last-wins
  swaps; this argument does not extend to them. That half is closed separately
  in `glob_ungate_swaps_import_winners_2026-08-01.md` (four independent proofs;
  323 rows = 280 callables + 43 constants; 99 of 160 provider pairs genuinely
  divergent yet still unobservable on every normal lane).
- No stage3 error-count table is reported: the run at this tip exited 143
  (SIGTERM), and per `glob_ungate_swaps_import_winners_2026-08-01.md` a count
  census is structurally blind to winner swaps anyway.

## Re-verification 2026-08-17

The two `TypeAlias` symbol-creation sites this doc cites
(`module_lowering.spl:632`, `module_lowering.spl:1855`) and the
alias-target consumers (`alias_registry.spl:211-217`,
`module_surface.spl` copy-only read) live under `src/compiler/20.hir/` and
`src/compiler/35.semantics/lint/semantic_api/alias_registry.spl`. The actual
defect — `SymbolTable.define` last-write-wins for `SymbolKind.TypeAlias`, and
`lower_named_kind` never expanding an alias — is owned entirely by
`src/compiler/20.hir/` (symbol table + `hir_lowering/types.spl`), which is
outside this worker's scope lock (`30.types, 35.semantics, 90.tools,
95.interp`). `alias_registry.spl` itself only reads the already-collapsed
`module.type_aliases` dict passed in; it does not participate in the
last-write-wins symbol definition and has no fix to make on its own.

Status unchanged: latent, no live miscompile today (confirmed by this doc's
own probe matrix), becomes live only once alias transparency is implemented
in `20.hir`.

**Verdict: BLOCKED (real fix belongs in `src/compiler/20.hir/`, out of scope
for this worker). No code change made.**

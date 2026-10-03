# Seed trait/Any method binding can discard receiver identity

## Observed evidence

The d6b569ace4 Stage 2 run compiled 1129 modules then failed linkage on missing
generated HIR helpers. Its selected object relocations nevertheless prove:

- `BlockRegistry.register` and two registry helpers invoke `SqlBlockDef.kind`
  for an `Any` receiver, after two scans report multiple candidate owners.
- Sync `Read.read_all` and `Write.write` delegation selects `ShbReader` and
  `SmfWriter` respectively.
- Async wrapper delegation selects the enclosing wrapper method itself.

Evidence lives at `D:/dev/bootstrap-failure-catalog-20261002/currentd6`.
Seed SHA: `465cd186f65f743b7accf65b3d2510220e450f3fd0635bae15acf559c3a12e7e`.
The inspected `closures_structs.rs` is unchanged between seed source
70e835667a and this lane's release base 1538f7da26. No runtime reachability
or successful executable is inferred from these relocations.

## Narrow correction

1. Qualified fallback compares complete owner components: `Read` is not a
   substring-based match for `ShbReader`.
2. An ambiguous cross-module scan stays unresolved; a later bare import entry
   cannot override that ambiguity.
3. An unresolved qualified owner is never discarded to select a bare method.
4. Cross-module aliases honor the existing bare-call self-recursion guard.

Exact qualified imports and ordinary builtin fallback remain available. This
patch does not implement missing runtime trait dictionaries or erase a
diagnostic. An unsupported dispatch shape may still reject or reach the
existing fail-closed function-not-found path; that is not semantic success.

## Acceptance

The production Rust owner-matching tests cover exact and module-qualified
owners, trait-name substring collisions, and wrong method names.
`test/fixtures/compiler/seed_trait_dispatch` supplies actual cross-module
registry and reader/writer calls with distinct results for each concrete
receiver. Require exit 0 and `seed-trait-dispatch: PASS` for semantic acceptance
on each host. Compile rejection or runtime failure is a remaining feature gap,
even if wrong-target relocations disappear. Retain both structural and runtime
results separately; do not classify warning disappearance as PASS.

Current status: source correction and fixtures implemented; Rust suite and
rebuilt-seed native execution UNRUN pending resource admission and review.
No existing frozen bootstrap source or cache was modified.

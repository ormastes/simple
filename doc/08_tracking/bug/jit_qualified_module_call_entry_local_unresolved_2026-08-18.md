# Qualified `use prov` + `prov.f()` in entry module still fails codegen (GlobalLoad 'prov')

**Status:** OPEN
**Filed:** 2026-08-18

Probe (fails on both the deployed seed and a fresh build WITH the
bare-assign-local minting fix, so it is independent of that change):

```
use prov
fn main():
    n = prov.provider_len("hello")   # -> GlobalLoad: unresolved identifier 'prov'
```

`check-import-alias-codegen.shs` PASSes its `qualified` fixture, so this shape
differs from the gated one (entry module + result assigned to a bare local).
Interpreter lane prints QUAL-OK. Discovered during rt_-alias lane-parity
probing (binary_runtime_hardening). Related:
`aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`.

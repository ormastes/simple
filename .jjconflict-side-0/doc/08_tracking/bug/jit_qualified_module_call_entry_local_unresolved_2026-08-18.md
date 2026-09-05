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

## Scope correction (2026-08-18, later): qualified is broken in codegen GENERALLY — the 2026-08-10 "fix" was verified through silent fallback

With the strict-JIT fail-open fix now in the deployed binary, the alias gate's
own `qualified` fixture (`use target` + `target.base_get("x")` in a MID module
— no entry-module shape, no bare assignment) fails deterministically:
`codegen: 1 function body/bodies failed to compile: [mid_call]`, twice in a
row, no timeout. Previously this exact failure was UNTAGGED, so it silently
fell back to the interpreter, printed the expected output, and the gate
reported `ok qualified` — a false green. Every earlier PASS of
`check-import-alias-codegen.shs`'s qualified row (including 2026-08-10's
"qualified fixed" claim in
aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md) must be
re-read with this in mind: the interpreter produced the V:x, not the codegen
lane. The gate now correctly shows the defect; leave it RED per testing rules
(a correct check that fails is a legitimate artifact) until qualified binding
is actually implemented in the codegen lane.

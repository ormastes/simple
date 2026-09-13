# Every symbol of `compiler.35.semantics.macro_contracts` is undefined in the compiled spec lane

- Status: OPEN (2026-09-12)
- Area: compiler / 35.semantics, SMF lowering, spec harness
- Severity: medium (any unit spec importing this module loses its whole file in every
  directory run; single-file runs hide it completely)
- Found by: TODOFIX-0 lane while adding a spec for todo 4. Not fixed — the defect is in the
  module's SMF compilability, not in any spec.

## Symptom

`test/01_unit/compiler/semantics/macro_contracts_spec.spl` is green single-file
(`outcome=OK declared>=10 executed=10 passed=10 failed=0`, interpreter lane) and collapses
in a directory run (compiled/SMF lane):

```
SPEC FILE VERDICT: ...macro_contracts_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1
error: compile failed (..._spec_native.spl): semantic:
  Undefined("undefined identifier: MacroContractItem")
```

## It is the module, not the spec

I reshaped the spec to name no struct type and read no struct field — the workaround that
fixed the same class of collapse for `text_diff_spec` (4e7ef7d279c). The error simply moved
to the next imported name:

```
Undefined("undefined identifier: process_macro_contract")
```

`process_macro_contract` is the module's principal function, not a type. Every name imported
from `compiler.35.semantics.macro_contracts` is unresolvable on the SMF path, so the module
as a whole never compiles there and no spec-side reshaping can rescue it. The speculative
accessors added while chasing this were reverted for that reason.

Likely contributors, all visible in the module and all porter artifacts:
`process_macro_contract` is declared `-> text` but returns `Ok(result)` / `Err(...)`; the
module uses the `.?` presence operator; the struct types are declared AFTER the function
that consumes them.

## Repro

```
bin/simple test test/01_unit/compiler/semantics/macro_contracts_spec.spl   # OK 10/10
mkdir -p test/01_unit/zz_probe && cp test/01_unit/compiler/semantics/macro_contracts_spec.spl test/01_unit/zz_probe/
bin/simple test test/01_unit/zz_probe/                                     # ERROR executed=1 failed=1
rm -rf test/01_unit/zz_probe
```

A 1-spec temp directory reproduces it in ~1 minute instead of the ~25 minutes the real
102-spec `test/01_unit/compiler/semantics/` directory takes. Pairing the spec with a
known-good neighbour (`gpu_mesh3d_spec.spl`, `OK 12/12/0` in the same run) proves the
harness itself is fine.

Binary: Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`.

## Related

Same *class* of silent whole-file loss, different causes, both measured the same day:
- `doc/08_tracking/bug/gpu_lighting3d_spec_asserts_stale_light_buf_field_2026-09-12.md`
- `doc/08_tracking/bug/devhub_cmd_daily_debug_spec_undefined_print_raw_in_compiled_lane_2026-09-12.md`

A spec whose SMF compile fails with "N function(s) contain constructs that require the
interpreter" DEGRADES to the interpreter and still runs; one that fails with `Undefined(...)`
or `HIR lowering: Unsupported feature` does not. Making the hard failures degrade the same
way would convert all three from silent file loss into ordinary passing runs.

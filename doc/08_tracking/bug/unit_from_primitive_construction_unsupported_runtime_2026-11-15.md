# Unit construction from a primitive is unsupported at runtime (blocks stdlib boundary migration)

Found by lane stdlibmig, 2026-11-15, with `bin/simple.exe run` on a file declaring
`unit FreeBytes: i64 as fbytes`:

- `FreeBytes(5)` -> `error[E1002]: function FreeBytes not found`
- `5 as FreeBytes` -> `semantic: type mismatch: cannot cast i64 to FreeBytes`
- only the literal suffix `5_fbytes` constructs a value; `.value` also fails JIT type inference.

SPL-BOUND-001/002 tell authors to build the unit inside an
`@unsafe(capabilities: [ffi])` adapter (`Unit(raw)` / `raw as Unit`), which is
therefore not executable today. Migrating a stdlib boundary (slice H) would break
runtime callers. Needs: a working primitive-to-unit constructor in the runtime
path (repro: the 4-line file above). Repro/prevention spec to be added with the fix.
Status: open. Baseline: doc/08_tracking/test/robust_boundary_stdlib_census_2026-11-15.md

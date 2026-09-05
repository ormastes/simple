# std.spec no longer exports SPipe — dependent specs pre-existing RED at HEAD (2026-08-26)

## Symptom
Any spec importing `use std.spec.SPipe` fails at load:

```
error: runtime: Module "std.spec" does not export 'SPipe'
Results: 1 total, 0 passed, 1 failed
```

Verified at HEAD (file restored via `git show HEAD:...`, 2026-08-26):
- `test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl`

The spec's 29 declared examples execute zero.

## Handling
Left RED per testing rules; sspec-maintain modernization for affected files
deferred until the import resolves (score fixes are unmeasurable on a spec
that cannot load).

## Unblock condition
Either `std.spec` re-exports `SPipe` (e.g. `use std.spipe.*` re-export) or the
spec's import is corrected to the module that now provides `SPipe`.

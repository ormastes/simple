# Function-body-scoped `use <path>.{name}` is a silent no-op for symbol resolution

- **Filed:** 2026-08-18
- **Status:** OPEN (compiler defect). Two call sites worked around by hoisting.
- **Severity:** HIGH — fails at call time with a "function not found" error that
  points at the callee, not at the import, so it reads as a missing/unexported
  function. Two independent agents misdiagnosed it on 2026-08-17/18.

## Symptom as first reported

```
error[E1002]: function `update_smf_manifest_entry` not found
```
fired POST-LINK on every *successful* native build taking the AOT `both`
output-format branch (`src/compiler/80.driver/driver_aot_pipeline.spl`), so the
link succeeded and then the build died before producing a binary.

## Root cause

A `use <module path>.{name}` written inside a function/method BODY registers
nothing. The parser accepts it, no warning is emitted, and the named symbol is
simply not in scope at the call site. Only module-scope `use` resolves.

This is NOT an arity mismatch, NOT a circular import, NOT an export gap, and
NOT specific to `update_smf_manifest_entry` — the definition
(`src/compiler/80.driver/watcher/smf_manifest.spl:340`) and export
(`watcher/__init__.spl:37`) were both correct all along.

## Minimal reproduction (verbatim)

`rep3.spl`:
```
fn main():
    use compiler.driver.watcher.smf_manifest.{smf_manifest_path_for_smf}
    print("{smf_manifest_path_for_smf("/tmp/x/a.smf")}")
```
```
$ bin/simple run rep3.spl
[jit-fallback] unresolved external symbol 'smf_manifest_path_for_smf': whole module dropped to the interpreter ...
error[E1002]: function `smf_manifest_path_for_smf` not found
  = help: check the function name or import the module that defines it
```

Moving the identical `use` line to module scope makes the same program run and
print `/tmp/x/manifest.sdn`. Binary under test:
`bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed, v1.0.0-RC).

## Workaround applied (does not close this bug)

Imports hoisted to module scope, call sites unchanged:

- `src/compiler/80.driver/driver_aot_pipeline.spl` — `source_to_cache_path`,
  `update_smf_manifest_entry` (this was the reported build blocker).
- `src/compiler/80.driver/watcher/watcher_daemon.spl` — `compile_to_smf_with_options`,
  `source_to_cache_path`, `update_smf_manifest_entry`. Same latent defect;
  `generate_smf` could never have resolved those three symbols.

Both files' modules were verified to load after the change with no import cycle.

## Real fix (not done here — out of scope of the build-unblock)

Either make body-scoped `use` actually bind into the enclosing scope, or reject
it at parse time with a diagnostic naming the import. A silently-ignored import
statement is the worst of the three options. Note the diagnostic must also
improve: E1002 currently blames the callee and never mentions that an import in
scope was discarded.

## Audit

Other body-scoped `use` sites in the tree are latent instances of this bug and
should be swept:

```
/usr/bin/grep -rn '^\s\+use [a-z]' src/ --include=*.spl
```

## Regression coverage

`test/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.spl`
pins the fixed AOT contract (module-scope import + the exact 10-argument
`update_smf_manifest_entry` call shape + manifest read-back). Proven RED with
the body-scoped import form (`semantic: function `source_to_cache_path` not
found`, `Results: 1 total, 0 passed, 1 failed`) and GREEN with module scope
(`Results: 1 total, 1 passed, 0 failed`).

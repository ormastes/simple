# Triage of the 2 crash-investigation byproduct defects (Round 2)

- Status: 1 FIXED (`build_targets_spec.spl`), 1 filed as another lane's in-flight work (`c_backend_export_spec.spl`)
- Binary: `d4c0779cef6cf0cc4054` / rebuilt `57761d4fbfed5e444a36`
- Base: `work/unit-p1-2026-09-13` at `5b13341d33b`

These two were found as a byproduct of Round 2's `child died by signal`
investigation (`child_died_by_signal_is_host_load_from_concurrent_sweeps_2026-09-13.md`):
both crashed under 3-way concurrent load, then reproduced as ordinary,
non-crashing failures once rerun alone on a quiet host. That doc asked for
each to get its own triage; this is it.

## 1. `test/01_unit/compiler/backend/c_backend_export_spec.spl` — FILED, not fixed

**Repro**: `bin/simple test test/01_unit/compiler/backend/c_backend_export_spec.spl`
-> `4 examples, 4 failures`, every one:
```
semantic: variable `MirToC` not found
```

**Cause, confirmed**: the spec imports `use compiler.backend.{MirToC}` (line
46). `MirToC` is genuinely defined
(`src/plugins/backend_c/_CBackendTranslate/class_core.spl`) and genuinely
re-exported — but only at `compiler.backend.backend.{MirToC}` (note the
doubled `backend`: `src/compiler/70.backend/backend/__init__.spl:46,51`), not
at the top-level `compiler.backend` the spec imports from
(`src/compiler/70.backend/__init__.spl`). That top-level `__init__.spl`
carries the line, verbatim:
```
# Bitfield re-export temporarily disabled while backend module path cleanup is in progress.
```
`git log -3 -- src/compiler/70.backend/__init__.spl` shows the disabling
commit is `e0fa5ef45e2` (2026-09-07), titled *"WIP: harmonize bootstrap
references and migrate kernel plugins (#319)"* — an explicitly WIP, in-flight
module-path migration by another lane. Not a spec typo; the spec's import
path was correct until that migration temporarily broke it.

**Not fixed here**: re-enabling the re-export means touching a module-path
migration mid-flight, owned by whoever landed #319 — exactly the class of
change this lane's rules say to leave alone (compare
`module_surfaces_from_owners`, `hir_pattern_tags` etc. in the original
receipt's remaining-failures section). If `compiler.backend.backend.{MirToC}`
(the doubled path) is confirmed to still work, importing from THAT path
directly would be a one-line spec fix — not attempted here because it wasn't
verified whether the doubled path is itself stable or also mid-migration.

## 2. `test/01_unit/app/build/build_targets_spec.spl` — FIXED

**Repro (before fix)**: `1 failed` (of 34), `it "rejects absolute and
parent-traversing output declarations"`:
```
expected false to equal true
```

**Cause, confirmed and already half-documented in the file itself**: lines
275-276 called `_has(...)`, but the file's OWN comment at lines 39-43
explains that `_has` was already found to collide with a differently-behaved
`_has` in `app.build.targets.change_classifier` (equality semantics, not
substring) due to a genuine interpreter defect — **free functions are
resolved by NAME across co-compiled modules, ignoring module boundaries** —
and was renamed to `_has_error` (substring semantics, defined at line 44) for
that reason. Two call sites in the one failing example were never updated to
match the rename. `validate_targets` (`src/app/build/targets/build_targets.spl:275-278`)
was never broken — `t.output.starts_with("/")` and `t.output.contains("..")`
both push `"target-error: unsafe-output: " + t.name + ...`, which DOES
contain the needle `"unsafe-output: a"` as a substring; the bug was purely in
which `_has` got resolved at the call site.

**Fix**: `_has(` -> `_has_error(` at the two sites. RED: `34 total, 33
passed, 1 failed`. GREEN: `34 total, 34 passed, 0 failed`.

**Not addressed, deliberately out of scope for this fix**: the file's own
`FIXTURE_ROOT` constant (line 30) is hardcoded to an absolute path from a
DIFFERENT session's scratchpad
(`/tmp/claude-1000/-home-ormastes-dev-pub-simple/2e5c44bf-.../scratchpad/build_targets_fixture`)
— a stale artifact from whoever last edited this file, not this lane. It
happens not to matter for the fixed example (the unsafe-output check does not
depend on the fixture existing), so nothing broke; flagged here in case
another example in this file depends on that directory actually existing on
this host.

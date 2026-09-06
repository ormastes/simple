# arm64 and riscv64 embedded GUI entries import but never call `install_generated_simpleos_wm_theme()`

Date: 2026-09-06
Status: open
Severity: P3 (visual regression: generated Aetheric base theme is never installed before the CSS override runs)
Location:
- `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:40` (import), no call site
- `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` (import present per
  `test/01_unit/os/wm_theme_bootstrap_contract_spec.spl` scenario "installs the generated
  Aetheric snapshot before RV64 compositor creation"), no call site
- Working reference: `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:324`
  (`val theme_snapshot = install_generated_simpleos_wm_theme()`)

## Symptom

`test/01_unit/os/wm_theme_bootstrap_contract_spec.spl` scenario "installs the
same generated Aetheric snapshot before ARM64 compositor creation" fails:

```
expected -1 to be greater than 0
```

`source.index_of("install_generated_simpleos_wm_theme()")` returns -1
because the call text is not present anywhere in the arm64 file, even
though the symbol is imported at line 40:

```simple
use os.compositor.simpleos_wm_theme_bootstrap.{install_generated_simpleos_wm_theme, apply_simpleos_css_theme_override}
```

Confirmed via direct grep:

```bash
grep -n "install_generated_simpleos_wm_theme(" examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl
# (no output)
grep -n "install_generated_simpleos_wm_theme(" examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl
# 324:    val theme_snapshot = install_generated_simpleos_wm_theme()
```

## Impact

The arm64 (and apparently riscv64) embedded desktop entries only run
`apply_simpleos_css_theme_override(theme_css)` against whatever compositor
default is in effect -- they never install the generated Aetheric base
snapshot the way x86_64 does before applying the boot-time CSS override.
Only x86_64 matches the documented three-architecture contract this spec
was written to enforce.

## Fix

Add `val theme_snapshot = install_generated_simpleos_wm_theme()` (or
equivalent) before compositor/engine creation in both
`examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl` and
`examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`,
matching the x86_64 call site's position (before
`create_fb_engine_sized(...)`). Out of scope for this session (test-file-only
batch on `test/01_unit/os/wm_theme_bootstrap_contract_spec.spl`); left for
the owning SimpleOS/compositor session.

## Related

This is one of several distinct pre-existing REDs in
`wm_theme_bootstrap_contract_spec.spl` (11 of 12 scenarios failed both
before and after this session's spec-modernization pass); most of the
others are `expect(source).to_contain(...)` string-drift failures against
unrelated modules, not this specific missing-call defect. See the
per-scenario `# NOTE:` comments in that spec file for the rest.

## Recovery note (2026-09-06)

This record was accidentally lost once during authoring -- a concurrent
peer session's working-copy sweep reverted three sibling spec files in this
same batch (`vfs_pure_fat_production_guard_spec.spl`,
`simplebox_dispatch_spec.spl`, and this bug's own
`wm_theme_bootstrap_contract_spec.spl`) back to their pre-modernization
content, and this untracked bug file vanished along with it. All four were
rewritten and re-verified (score + runtime pass count) after the fact. This
is the documented shared-working-copy risk noted in
`.claude/rules/vcs.md` / project memory: untracked files in this checkout
can be swept by peer sessions mid-edit.

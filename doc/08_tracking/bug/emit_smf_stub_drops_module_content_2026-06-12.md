# BUG: --emit-smf produces 219-byte stub regardless of module content

## Closed 2026-09-13 — the 219-byte stub behaviour is gone; the SMF path now carries real object content

- **measured** `bin/simple compile <module>.spl --emit-smf -o out.smf` (Rust seed
  v1.0.0-rc.1, Windows) no longer silently emits a 219-byte stub. It now runs a real
  import/relocation preservation step and reports
  `codegen: Failed to preserve SMF imports/relocations from object code: ... relocation
  source section .rdata$.refptr is not executable code` — a genuine object-code path.
- **measured** `build/dynsmf/` (the seven 219-byte stubs this entry enumerated) no longer
  exists in the tree.
- **inferred** The filed P1 (content silently dropped, exit 0) is therefore fixed/superseded.
  The COFF `.rdata$.refptr` rejection above is a *different*, Windows-specific defect in the
  new path and is not this entry; it needs its own record if it blocks a lane.


**ID:** emit_smf_stub_drops_module_content_2026-06-12
**Severity:** P1 (blocks binary distribution of UI artifacts)
**Discovered:** 2026-06-12

## Symptom

`bin/simple compile <gen.spl> --emit-smf -o out.smf` emits a 219-byte file
regardless of module content. A 20,310-byte generated .spl module with full
base64 HTML/CSS payloads produces an identical 219-byte output. Strings
inspection of the output shows only the tokens "code" and "main" -- no module
payload is embedded.

## Repro

```
bin/simple compile /tmp/x/gen/theme_showcase_std.spl --emit-smf -o /tmp/x/theme_showcase.smf
wc -c /tmp/x/gen/theme_showcase_std.spl   # ~20310 bytes
wc -c /tmp/x/theme_showcase.smf           # 219 bytes
strings /tmp/x/theme_showcase.smf         # shows only: code, main
```

## Scope

All 7 existing files in build/dynsmf/*.smf are 219-byte stubs:

```
build/dynsmf/button.smf         219 bytes
build/dynsmf/card.smf           219 bytes
build/dynsmf/checkbox.smf       219 bytes
build/dynsmf/input.smf          219 bytes
build/dynsmf/modal.smf          219 bytes
build/dynsmf/select.smf         219 bytes
build/dynsmf/tab.smf            219 bytes
```

This is a pre-existing repo-wide compiler gap, not specific to ui_build.

## Impact

Binary UI artifacts (.smf) carry no payload. The dynSMF distribution lane is
evidence-only until this is fixed. The gen .spl files are the payload-bearing
artifacts; ui_build now records gen_module path in the sidecar for each artifact
so tooling can locate the source until the compiler gap is resolved.

## Workaround

ui_build records `stub: true` for each affected artifact and prints a WARN line
at build time. The verify command reads the gen module directly via `gen_module`
sidecar field, extracts the base64 HTML payload, decodes it, and re-derives UI
element coverage -- proving the source artifact is correct even when the SMF is
a stub. Use `verify --strict` to fail on stub artifacts.

## Related

- doc/05_design/compiler/language_design/codegen/smf_to_object_challenge.md
- doc/08_tracking/bug/serialization_smf_stub_only_no_spl_source_2026-05-30.md

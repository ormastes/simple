# Target 5 Stage4 legacy character helper omitted from exact C capsule

- **Status:** Fixed in source; Stage4 link proved on 2026-09-29
- **Found:** 2026-09-29, Linux aarch64 Stage4 + lld compiler entry
- **Impact:** blocks the admitted Stage4 compiler and hello size/startup/RSS cohort

The current-source pure-Simple bootstrap tool compiled all 866 compiler-entry
units with zero failures. Its exact provider checks and capsules passed, then
the final lld link failed on `text_dot_from_char_code` from COFF linker
modules (`mod_519.o`, `mod_521.o`). The selected Stage4 core-C archive
defines that symbol in `runtime_native.o`, but
`stage4_live_runtime_requests` selects only `rt_*`, `spl_*`, and a short
runtime-control list. It therefore omits this legacy compiler ABI helper,
and core-C capsule projection localizes the definition.

The saved live partial-link object has 304 undefined names. Comparing these
with the selected core-C and compiler backfill archive definitions finds
exactly one provider-owned name outside `rt_*`/`spl_*`:
`text_dot_from_char_code`.

The exact live runtime request set now includes this helper. The current-source
Stage4 + lld build compiled 866 units with zero failures and linked an
executable with the no-stub owner gate. Its `--version` smoke passed. Hello AOT
still fails at `PLUG-E-NOTFOUND: backend=llvm`, tracked separately in the K1
composition-shadowing bug; no hello executable or size qualification is claimed.
This AOT capsule omission is distinct from the older seed JIT symbol-table issue in
`seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`.

Evidence: `doc/09_report/compiler/target5_stage4_live_projection_linker_2026-09-29.md`.

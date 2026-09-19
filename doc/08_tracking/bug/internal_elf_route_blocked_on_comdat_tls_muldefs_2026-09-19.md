# internal:elf route now carries the native_all table but is still blocked on COMDAT / TLS / muldefs

Status: OPEN — recorded by lane G1, not implemented here (out of scope by
assignment; the engine work belongs to the lane that owns
`elf_static_link.spl`'s feature surface).

## What changed, and why that exposes these

`link_native_unix`'s `SIMPLE_LINKER=internal` branch used to call
`internal_link_native` with no archives, no libraries and no roots. It now
assembles the same inputs the external argv path does (`internal_link_plan`,
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`):

* the selected runtime bundle's static archives (`core-c-bootstrap` ->
  `libsimple_compiler_backfill.a` + `libsimple_native_all.a`),
* the `native_all_gnu_support_args` table split into `libraries` (8 `-l`
  names) and `roots` (`-u rt_vulkan_provider_is_available`, now
  `ElfLinkRequest.roots`),
* `config.libraries` / `config.library_paths`.

Before this, the internal route fed the engine only the caller's objects, so
none of the blockers below could ever be reached. Feeding it
`libsimple_native_all.a` is what makes them live.

## The blockers (measured in the Fable decision, 2026-09-19)

`libsimple_native_all.a` is 373 MB / 3365 members and carries:

| feature | corpus count | engine today |
|---|---|---|
| `SHT_GROUP` (COMDAT) | 122,328 sections | header says "no COMDAT dedup"; `gc_sections.spl` errors on `SHT_GROUP` |
| TLS (`SHF_TLS` relocs) | 751 relocs | `elf_static_link.spl` hard-`Err`s on `SHF_TLS` |
| duplicate definitions | ~7 Simple-side dup symbols | `sym_resolver.spl` refuses; needs a first-wins flag |

The admitted Stage 2 binary has `PT_TLS` and 461 TLS symbols, and the C
runtime has 38 `__thread` sites, so TLS is not avoidable by input selection.

These are all *refusals*, not silent wrong output, which is the correct
failure mode: a Stage 3 link with `SIMPLE_STAGE3_LINKER=internal` on today's
engine stops with a named engine error rather than emitting a bad binary.

## What is needed

1. COMDAT group dedup (`SHT_GROUP`) in the engine, and the matching removal of
   the `gc_sections.spl` rejection.
2. TLS: local-exec and TLSDESC per the corpus census, plus `PT_TLS` emission.
3. A first-wins multiple-definition flag in `sym_resolver.spl` for the handful
   of Simple-side duplicates.

Until those land, `SIMPLE_STAGE3_LINKER=internal` is an opt-in knob that is
expected to fail loudly on the real bootstrap corpus. It defaults OFF and
changes no existing receipt hash.

## Related

* `scripts/check/lib/bootstrap-stage3/authority.shs`
  (`bootstrap_stage3_linker_env`) — the knob.
* `test/01_unit/compiler/backend/linker/internal_native_all_support_spec.spl`
  — the route/roots evidence.
* `test/01_unit/compiler/bootstrap/stage3_linker_knob_spec.spl` — the knob
  evidence.

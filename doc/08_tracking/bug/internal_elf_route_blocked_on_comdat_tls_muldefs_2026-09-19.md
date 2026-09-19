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

## The knob cannot complete a RESUME flow yet (separate, real gap)

`bootstrap_stage3_manifest_verify_transcripts`
(`scripts/check/lib/bootstrap-stage3/manifest-verify.shs:665-701`) recomputes
the expected Stage 3 args hash from a **fixed, hand-written env list**. That
list has no `SIMPLE_LINKER` — and, pre-existing and unrelated to this lane, no
`stage3_mc_env` (`SIMPLE_SAFETY_PROFILE`/`SIMPLE_ASSURANCE_WARNING_PHASE`) and
no `stage3_cold_init_env` (`SIMPLE_SCV_INVENTORY_COLD_INIT`) either. So a
knob-ON Stage 3 records a hash the verifier cannot reproduce, the comparison
at :701 fails, and the resume rebuild dies at
`scripts/bootstrap/resume-stage3-from-admitted.sh:915` under `set -eu`.

It **fails closed**, which is the correct direction: a knob-ON build is never
admitted against a knob-OFF expectation. But it means `SIMPLE_STAGE3_LINKER=
internal` can produce a Stage 3 candidate and cannot yet carry it through the
resume/admission flow.

**In scope for the next lane**, and it is the cheapest of the four items here:
the fix is to make that list derive the three opt-in fragments the same way
the bootstrap scripts do (`bootstrap_stage3_linker_env` and the two existing
`case` blocks) instead of hard-coding the knob-off vector. Fixing it for
`SIMPLE_LINKER` alone would leave the two pre-existing omissions in place, so
the three should move together.

## Deliberate divergences from ld.lld on `-u` (keep, but know about them)

`elf_static_link.spl` (the root check after symbol resolution) is STRICTER
than lld in two ways. Both are intentional:

1. **A root nothing defines.** `ld.lld -u foo` with no definition exits 0 —
   it adds an unreferenced `Undefined` and `reportUndefinedSymbol` skips it.
   This engine returns `Err("root symbol not defined: foo")`.
2. **A root exported only by a shared library.** lld exits 0. This engine
   still Errs, because it emits a dynamic symbol only for a real reference
   from an input object, so "kept" would be a claim it cannot honour.

Rationale: on this route a `-u` exists to retain an archive member. Silently
accepting a root that retained nothing is the failure mode the route already
had. If a future caller needs lld's laxer behaviour, that should be an
explicit request field, not a change of default.

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

## Non-blocking gap: `-lgcc_s` linker scripts that use `-l` for their members

Found by review, 2026-09-19. gcc ships `libgcc_s.so` as a linker script whose
body is `GROUP ( libgcc_s.so.1 -lgcc )`. `ld.lld` resolves the `-lgcc` member
through its own `-L` search path. `internal_linker_script_target`
(`native_linking.spl`) only resolves members that name a FILE — absolute, or
relative to the script's own directory — so it finds `libgcc_s.so.1`, which is
the member that matters, but if that member were absent it would refuse with
"naming no readable ELF member" where lld would still succeed via `-lgcc`.

Impact today: none of the eight libraries in the native_all table is affected;
this bites only a `-lgcc_s` that reaches the internal route.

The proper fix is to make the script follower recursive — a `-l<name>` inside a
GROUP re-enters `internal_resolve_library` with the same search directories.

**Possibly moot:** lane T1 is removing the GCC dependency in favour of
LLVM/compiler-rt. If that lands, `-lgcc_s` disappears from every table and this
gap has no caller. Recorded anyway, because "another lane may delete the
caller" is not the same as "this is correct".

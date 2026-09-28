# Target 6 persisted archive publication candidate

Status: focused native publication PASS; compiler-driver call remains open.

`cold_hir_package_publication_v1.spl` builds the compact V2 graph, admits one
persisted CAS archive per package, compares the actual interface/action member
hashes with each compact output, and moves the package-index pointer only after
all packages pass. It checks the exact three-member byte layout and archive
manifest, rejects a changed CAS batch generation, uses pointer CAS, and reads
back the published graph. It holds one archive at a time rather than retaining
HIR modules, source bodies, or all archive bytes.

The integration spec extends the compact typed-HIR graph fixture with a real
CAS archive publication and two cases: successful graph publication, and a
stale interface payload digest that must leave index `CURRENT` absent. The
archive fixture's other scalar output digests are still synthetic, so this
does not prove the production codegen receipt producer or full driver cutover.

Three bounded native build/fix attempts exposed the staged runtime closure:

1. Importing the warm pinned archive decoder required 40 unsupported runtime
   symbols, including file-view, async-driver, and network entry points.
2. CAS readback with strict member hashes removed file-view calls, leaving 26
   async/network symbols. Changing the CAS batch file-lock import from the
   broad `std.io` facade to its `std.nogc_sync_mut.io.file_ops` owner removed
   those external-symbol failures.
3. The next link failed on one internal `char_from_code` symbol. The final
   candidate converts each expected text member with the existing strict UTF-8
   converter and hashes its text bytes; it has not been rebuilt after that
   change because the session reached its three-attempt cap.

At that point, the next planned run was the four-example native spec. The
focused PASS below resolves that check; compact typed-HIR and compiled-output
receipts still need production driver wiring before warm/cold native time and
RSS cohorts can qualify Target 6.

## Focused Stage2 native publication PASS

After repairing optional receipt decoding and reading member bytes directly
from the admitted archive text, the no-stub Stage2 build of
`test/02_integration/compiler/cache/cold_hir_compact_output_index_spec.spl`
reported 4 examples and 0 failures. The persisted archive was decoded before
the V2 index pointer moved, and a mismatched interface digest left `CURRENT`
absent. The build compiled 3 changed units and reused 320 in 6.83 seconds
at 446,600 KiB peak RSS; the single spec run took 0.05 seconds at 5,536 KiB
max RSS. This is focused correctness evidence, not a paired performance
cohort or production driver cutover. The native `text.bytes()` bug remains
tracked separately.

## Native execution follow-up

The text-hash change alone still linked with an unresolved internal
`char_from_code` reference. The reference came from the interpreter's
`n.chr()` lowering; routing that call through the existing pure-Simple
Unicode converter produced a native executable. Execution exposed a separate
failure in the larger closure: reverse SMF section admission returns
`cold-reverse-section-invalid:smf-section-invalid` before any archive check.
The four-example spec reports 4 failures but exits 0. No publication PASS is
claimed. See
`doc/08_tracking/bug/target6_native_reverse_section_invalid_2026-09-29.md`.

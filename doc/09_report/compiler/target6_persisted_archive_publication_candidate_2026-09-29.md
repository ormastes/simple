# Target 6 persisted archive publication candidate

Status: candidate; native execution and compiler-driver call remain open.

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

Next run: compile and execute the four-example native spec once, repair any
remaining concrete failure within the next session's cap, then wire compact
typed-HIR and compiled-output receipts from the driver to this publisher.
Only after that can warm/cold native time and RSS cohorts qualify Target 6.

# Inventory validation scratch ownership

Executable: `test/01_unit/lib/scv/compile_source_inventory_validation_scratch_spec.spl`.

The four scenarios execute the production validator and encoder. They preserve valid fields, reject an invalid digest in each of the five facets plus parent-traversal paths and negative lengths, require a caller's scratch scope to remain open, and compare the complete canonical wire record with an independently constructed expected string.

Native resource fixture: `test/fixtures/bootstrap/inventory_validation_scratch.spl`. It executes 50,000 validations, requires zero growth in the runtime live-object registry, checks negative inputs and nested scope survival, and checks exact canonical bytes. Execute as a compiled native binary; interpreter counters do not establish native reclamation.

Qualification is pending. Creating these tests is not execution evidence. Full cold publication, peak RSS, paired elapsed measurements, and bootstrap qualification remain required.

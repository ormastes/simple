# Phase1 index wire error classification

The rebuilt Linux seed executes native_group_index_spec.spl: four examples pass and two reject the correct bytes with the wrong error classification. Appending non-newline trailing bytes causes BuilderWireReaderV1.create to record an invalid terminator; scalar then returns empty text, so the index receipt and handoff decoders report header errors instead of the required noncanonical-data errors.

Check the reader's construction reason before consuming the header. Preserve size bounds, header validation, field parsing, exact re-encoding, and rejection of trailing bytes. No malformed payload is admitted.

The two previously failing original example blocks pass on the rebuilt seed using a diagnostic harness with the original fixture definitions and unchanged example bodies. Four already-passing blocks were omitted. The first external harness ran zero examples because project-relative compiler imports could not resolve; moving the harness under the project fixed that execution setup. Enforcing watchdog evidence records exit 0, quiescent 1, peak 3307344 KiB, and maximum sample gap 3041 ms. Logs, source selection digest, result artifact and receipt are retained under /tmp/simple-index-classification-repair.

This is selected-case Phase1 evidence, not whole-suite qualification. The two production decoder files are loaded from the isolated fix checkout; the compiler snapshot is pinned to the canonical 3a329759303 seed generation. Phase2 and release admission remain pending.

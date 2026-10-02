# Named guest evidence is distinct from host success

**Manual draft; execution and docgen TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_named_guest_evidence_v1_spec.spl`.
Requirements: platform REQ-014 and REQ-016.

Resolve each represented named scenario and require a nonempty canonical
completion-marker list. Classify empty serial input and host-only success
text: each must report a missing marker. Classify the complete marker set and
require `ready` from the existing production scenario classifier.

These strings are deliberate unit inputs, not fabricated runtime receipts or
captured serial evidence. Live qualification still requires the separate
admitted CLI/QEMU route, actual process results and its actual serial section.

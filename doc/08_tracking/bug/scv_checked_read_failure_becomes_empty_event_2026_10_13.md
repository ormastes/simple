# SCV checked-read failure is converted to empty content

Status: concrete source defect; dynamic reproduction and candidate UNRUN. Bug DB reconciliation pending (qualified DB provider unavailable).

Frozen cce267e717684e7f87aea1603df3da7c0745258d `src/app/compiler_entrypoint/inventory_scratch.spl::compiler_inventory_file_event_v1` passes `file_read_text_at_checked(absolute, 0, 1073741824) ?? ""` to the canonical event constructor. The checked facade distinguishes failure (`nil`) from a successful empty file, but this expression erases that distinction before event creation. An earlier existence check does not prove a later read succeeds.

This is separate from the checked-reader cap allocation cost. No patch is included in that performance repair. It is not yet established whether downstream snapshot checks prevent publication in every failure path; this report does not claim that an invalid CURRENT was published.

Required focused reproduction: genuine unreadable/missing-after-check input yields no event; a readable zero-byte source still yields its authentic empty digest; transient scope cleanup happens on the failure path; no failed read can be admitted as successful empty content. Review retained-event promotion and cleanup before implementing an early nil return. Preserve whole-build failure and source authority gates.

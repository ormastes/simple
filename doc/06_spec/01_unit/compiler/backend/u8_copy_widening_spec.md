# Integer signedness after inferred local copy

Specification: test/01_unit/compiler/backend/u8_copy_widening_spec.spl

SSpec status: NOT_RUN under an admitted self-hosted compiler.

The cases require inferred local copies of unsigned octets 0, 127, 128, 153, 255 to
widen without sign extension, and signed i8 values -1, -128 to remain negative.
Direct LLVM owner cases also seed stale destination signedness and require
Copy and Move to emit `zext` for U8 and `sext` for I8. These new owner cases
are authored and NOT_RUN; no runtime claim follows from source inspection.
Store-owner cases additionally allocate an i64 slot, store a tracked byte,
and reload it. Unsigned U8 must emit `zext i8`; signed I8 must emit `sext i8`.
The signed native counterpart `i8_checked_window_native_probe.spl` keeps values
live across validation and checks the exact result `[-128,-1,0,127]`.
These added store/signed cases are NOT_RUN. The original unsigned checked-window
fixture remains byte-identical to its recorded failing version.
An earlier version of native fixture u8_widen_native_probe.spl passed 8 assertions with a
Hello-checked unadmitted pure-Simple compiler. See the versioned SDN evidence
recorded in doc/08_tracking/bug/native_tcp_byte_window_octet_representation_2026_11_07.md.
This does not qualify all integer casts or the full orchestrator transport.

Expanded regression adds range validation plus array push. Native diagnostic
counterpart currently FAILS (checkedWindowSucceeded=false for valid octets).
Ordinary inferred/annotated loops pass. The original 8-assertion pass does not
cover this newly added case. Repair loop stopped at six-cycle cap; no qualification.

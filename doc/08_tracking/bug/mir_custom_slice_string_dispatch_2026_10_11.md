# Unresolved custom slice incorrectly enters string runtime

Status: OPEN, draft compiler guard UNEXECUTED.

Actual Phase 4 ByteSpan fixture produced a 16616-byte object and linked successfully, then exited 1 on its first value check. Disassembly shows rt_interp_cstr and spl_str_slice for a ByteSpan receiver despite a ByteSpan.slice definition. Evidence owner: /home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/typed-span/{evidence,diagnosis}.json. The original chained receiver control separately fails MIR; result-only annotation is not a qualified workaround.

Draft: include slice/substring in existing primitive text receiver provenance probing and require that proof plus an empty static owner before entering unresolved string slicing. Preserve runtime array dispatch and ordinary custom resolution; evaluate receiver once via the existing prelowered local. This is a logic correction, not a performance or memory optimization.

Qualification requires actual ByteSpan prefix/slice comparisons, a colliding custom slice owner, runtime array slices, declared and inferred text substring/slice, and receiver side effects counted once. Check emitted callees and executed values. Guarding the wrong builtin alone is not proof that custom dispatch succeeds. The existing paired Phase 4 fixtures preserve the wrong-code and MIR failures; no PASS claimed.

Phase 4 owner exact two-hunk source review found no P0/P1: existing shared prelower flag preserves evaluation, array dispatch precedes string fallback, static owners excluded. New test/fixtures/native/custom_slice_owner/main.spl adds five value checks, AUTHORED_UNEXECUTED.

**Revalidated 2026-11-02: still plausible because OPEN, draft compiler guard UNEXECUTED; no merged fix commit with a passing regression is cited in this doc.**

**Triage 2026-11-03 (group C):** the draft guard (e14301086, `text_builtin_resolution_allowed and static_receiver_name == ""` on the substring/slice arm plus slice/substring in the primitive-text receiver shape) IS on release/1.0.0 (method_calls_literals.spl:3702 and :3748). Status -> fix-implemented-verification-pending. Verify: native-build test/fixtures/native/custom_slice_owner/main.spl, expect exit 0 and stdout exactly `custom-slice-receiver-once\n`.

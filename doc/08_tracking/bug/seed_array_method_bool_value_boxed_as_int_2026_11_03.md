# Typed array methods box Bool values as integers

Status: FIXED (P1, scoped typed-array Bool `.push` / `.index_of` boxing) — focused Rust MIR and direct native fixture passed; no Phase 2/3 qualification claimed.

## Static owner finding

In `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`,
`MirLowerer::lower_method_call` has array-receiver paths for `.push` and
`.index_of`. Both `needs_push_boxing` / needle boxing predicates include
`TypeId::BOOL`, and their fallback emits `MirInst::BoxInt`. That represents
Bool values as tagged integers before the runtime array method uses them.

The collection literal path in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` instead
uses `rt_value_bool` for Bool elements. This makes the method path inconsistent
with the array literal representation: `.push(true)` may store a different
tag, and `.index_of(true)` may search using a different tag. The separate
array-method paths were subsequently corrected and validated with the focused
evidence below.

Keep this issue separate from the multi-field and single-field enum constructor
paths.

## Focused verification (2026-11-03)

The producer source head was `3dd808aedbc279095c470ddba618d0fa7c230645` with
tracked source diff SHA-256
`9E170C1668B9E7E0E7BCFD1C1F1A03CA08B4483946D89F79F7A2A1068ABDB9D4`.
Four unique Rust MIR tests passed: typed Bool `.push`, typed Bool
`.index_of`, an integer `.index_of` boxing control, and the specialized raw-i64
`.push` control. The first three were in attempt 02 and the raw-i64 control
passed in attempt 03. Retained unit receipts:
`C:/dev/p3new/s2_enum_bool_batch_20261103/attempt_02/result.sdn`, SHA-256
`C2583A108CC4535F7A6600F3509D1841640A0DEFEA9C4915AD7D4330222549C4` (three
passed, one failed fixture case), and `attempt_03/result.sdn`, SHA-256
`77A082E09A515BF06BA8DF6F7A5D2D1382C9E5BDD7D1110CDF775CEF885667B6` (the
corrected single test passed). Together with the single-field test, the
campaign has five unique focused Rust tests passing. The initial fixture
failures and corrected test-only retry are preserved; fixture problems are not
counted as product failures or product fixes.

The dedicated native fixture `typed_array_bool` passed under producer SHA-256
`36F452B0CA65D46B5FD6F5457DDADE4F158B85BB2BA5900DE20737CFAB601456`; its
executable SHA-256 is
`3EF11AA6CFB6454E1694DD3685469CA90BA770BF7CE93A07F4C41E3A70F8A9E7`. The
aggregate result is `C:/dev/p3new/enum_array_bool_native_verify_20261103/attempt_01/result.sdn`,
SHA-256 `0B0CF11DC07B5DA8724F5000C501A83E8E5E1189A4F17BB9A643E2C66ED71B31`.
The fixture covers Bool `.push` and `.index_of` against Bool literals and
contains ten semantic checks. The campaign explicitly records
`phase2_qualification: false` and `phase3_qualification: false`.

The independent mechanism review passed against
`C:/dev/p3new/enum_array_bool_native_verify_20261103/attempt_01/mechanism_receipt.sdn`,
SHA-256 `790484CE7BF7206B9911448A476DECE01C20BF47781EF6FB1E8581A4F3D35A4C`.
It verified the typed-array Bool boxing path for `.push` and `.index_of` in
this scope; it does not extend closure to other BOOL boxing sites.

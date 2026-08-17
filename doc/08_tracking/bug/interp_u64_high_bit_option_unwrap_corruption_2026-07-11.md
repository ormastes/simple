# u64 struct field >= 2^63 corrupts `if val` Option unwrap after JIT shared-pointer bail

Status: FIXED 2026-08-17. **The title and the original diagnosis are both
wrong** — see the Correction below. Kept under this filename for traceability.

## Correction 2026-08-17 — this was never an Option bug

Reproduced live on the deployed seed, then root-caused to something else
entirely. `Option` is not involved, and the `u64` was never corrupted: the
stored value round-trips through `to_text()` perfectly at every magnitude.

The real defect: the interpreter's four ORDERING operators were **signed**.
Each of the `Lt` / `Gt` / `LtEq` / `GtEq` arms in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs` terminated at
`left_val.as_int()? OP right_val.as_int()?`, which reinterprets a
`Value::UInt { value: u64, .. }` as `i64`. Every `u64` at or above `2^63`
therefore compared as a **negative** number. Minimal proof (deployed seed):

```
val b: u64 = 9223372036854775808u64
b.to_text()  -> "9223372036854775808"   # storage always correct
b > 0u64     -> false                    # interpreter (WRONG)
b > 0u64     -> true                     # JIT
```

In this doc's own reproducer the guard `frame.checksum > 0u64` evaluated to
`false`, so `found` was never assigned and `find_valid` correctly returned
`nil`. The `if val f = ...` narrowing "failure" and the resulting
`unknown property or method 'checksum' on Option` were **downstream
consequences of a wrong comparison**, not a defect in `Option`, in `if val`,
or in the JIT shared-pointer bail. That the threshold sat at exactly `2^63`
was the tell — that is the i64 sign bit, not an Option or refcount boundary.

**Fix:** `unsigned_ordering()` in `interpreter/expr/ops.rs`, consulted first in
all four ordering arms. Mixed `UInt`/`Int` is defined explicitly (a negative
signed value is below every unsigned value; a non-negative one compares as its
`u64` widening) because Rust has no native mixed comparison and casting either
way reintroduces the same wrap.

**Gates:**
- `test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl` —
  reproducer. Before: `Results: 6 total, 3 passed, 3 failed`.
  After: `Results: 6 total, 6 passed, 0 failed`.
- `test/01_unit/language/unsigned_ordering_signedness_class_spec.spl` —
  similar-problem detection across all four operators, all three operand
  pairings (incl. the unsuffixed-literal `u64 > 0` mixed case the reproducer
  never touches), and the 2^63-1 / 2^63 / 2^64-1 boundaries.
  Before: `Results: 8 total, 2 passed, 6 failed`.
  After: `Results: 8 total, 8 passed, 0 failed`.

The detection spec failed **6** where the reproducer failed 3, i.e. it caught
strictly more of the class than the filed shape did.

**Not yet proven:** the fix is verified on a locally built seed only. The
deployed `bin/simple` still predates it and still reproduces; this closes only
once a bootstrap redeploys. The workaround masking to the low 63 bits in
`src/lib/common/ui/window_scene.spl` is now unnecessary but was left in place
rather than removed under a live bootstrap.

---

Original report follows (diagnosis superseded above).

Status: was OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Found while implementing Lane C nested content frames
(`test/02_integration/rendering/wm_nested_content_frame_spec.spl`,
`src/lib/common/ui/window_scene_draw_ir.spl`).

`common.ui.window_scene.wm_content_frame_checksum` (extracted from
`os.compositor.simple_web_window_renderer._simple_web_content_checksum`, same
XOR-hash algorithm, unchanged) returns a `u64` that is uniformly distributed
across the full 64-bit range — i.e. roughly half the time its high bit is set
(value >= 2^63, so it would print as negative if misread as a signed `i64`).

`_shared_wm_content_frame_for_window` (window_scene_draw_ir.spl) has this
shape (pre-existing, unrelated to this task's edits):

```
fn _shared_wm_content_frame_for_window(...) -> WmContentFrame?:
    var found: WmContentFrame? = nil
    ...
    for frame in input.content_frames:
        if <match>:
            val valid = ... and frame.checksum > 0u64 and ...
            if valid:
                found = frame
    if matching_count == 1:
        return found
    nil
```

`var found: WmContentFrame? = nil` triggers a JIT-to-interpreter bailout:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering
error: Memory safety error [W1003]: mutable binding with shared type (found):
shared pointers cannot be reassigned; use `val` instead of `var` at <line>
```

Under that interpreter-fallback path, when the returned `Some(struct)` has a
`u64` field whose value is `>= 2^63`, `if val f = fn_returning_option():`
fails to narrow `f` to the inner type — a later `f.field` access raises
`error: semantic: undefined field: unknown property or method 'checksum' on
Option`. The same struct/field access, and the same `frame.checksum > 0u64`
comparison, work fine as bare boolean expressions computed inline (outside
this reassign-inside-a-loop-then-return shape) even with the same >= 2^63
value — so the corruption is specific to the JIT-bail interpreter path
returning/rebinding an `Option<Struct-with-u64-field>` where the u64's high
bit is set, not to u64 comparison or struct field access in general.

## Repro (minimal, isolated from this task's code)

```simple
struct Frame:
    id: text
    checksum: u64

fn find_valid(frames: [Frame], target_id: text) -> Frame?:
    var found: Frame? = nil
    var matching_count = 0
    for frame in frames:
        if frame.id == target_id:
            matching_count = matching_count + 1
            val valid = frame.checksum > 0u64
            if valid:
                found = frame
    if matching_count == 1:
        return found
    nil

fn main():
    val small = [Frame(id: "a", checksum: 9223372036854775807u64)]  # 2^63 - 1
    val big = [Frame(id: "a", checksum: 9223372036854775808u64)]    # 2^63
    if val f = find_valid(small, "a"):
        print("small found checksum={f.checksum}")   # prints fine
    if val f = find_valid(big, "a"):
        print("big found checksum={f.checksum}")      # crashes:
        # error: semantic: undefined field: unknown property or method
        # 'checksum' on Option
```

Confirmed threshold is exactly `2^63` (`9223372036854775807u64` works,
`9223372036854775808u64` breaks) — i.e. the value is only broken once it is
unrepresentable as a non-negative `i64`, pointing at an internal tagged-value
representation that reinterprets/mishandles a u64 as signed somewhere in the
JIT-bail interpreter's Option-construction or pattern-match path.

## Impact

Any producer of a `u64` "provenance" value (content-frame checksums, hashes,
IDs) that can legitimately land >= 2^63 and is then wrapped in `Option<Struct>`
returned from a function shaped like the repro above is at risk — this
already existed latently in `os.compositor.simple_web_window_renderer`'s
original (pre-extraction) checksum consumer path before this task, since the
hash algorithm was unchanged.

## Workaround applied

`wm_content_frame_checksum` (`src/lib/common/ui/window_scene.spl`) masks the
hash to the low 63 bits (clears the sign-adjacent high bit) before returning,
so a checksum produced by this shared helper can never land in the broken
`>= 2^63` range. This preserves the algorithm's collision-resistance
properties (loses one bit of hash space, not a full redesign) while avoiding
the interpreter bug in practice. The interpreter/compiler bug itself is not
fixed by this workaround and should be root-caused separately (likely in the
tagged-value handling on the JIT-bailout interpreter path for
`Option<Struct>` unwrap, per the repro above).

Tracked in `doc/08_tracking/bug/bug_db.sdn` as
`interp_u64_high_bit_option_unwrap_corruption`.

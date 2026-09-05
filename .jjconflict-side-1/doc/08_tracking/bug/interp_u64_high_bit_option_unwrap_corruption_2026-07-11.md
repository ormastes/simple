# u64 struct field >= 2^63 corrupts `if val` Option unwrap after JIT shared-pointer bail

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

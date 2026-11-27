# Tiny GUI wheel deltas overflow before viewport clamping

Status: source repair; runtime verification unexecuted by explicit user waiver.

The GUI event dispatcher added the i32 wheel delta to the i32 scroll offset
before clamping. At offset 1, delta 2147483647 exceeds the signed i32 range;
wrapping arithmetic sends the viewport to the top instead of the bottom, and
checked arithmetic can trap before clamping. This is a source-level defect;
no runtime reproduction was executed in this session.

The dispatcher now uses the existing Tiny saturating-add owner, which widens
the operands before addition and clamps to i32. The existing viewport clamp
then limits the result to the actual content range. No renderer/backend or
platform-specific code is changed.

Authored regression: `test/01_unit/lib/tiny/gui_scroll_delta_bounds_spec.spl`.
Cases cover maximum positive delta from a nonzero offset, minimum negative
delta, repeated endpoint events, ordinary forward/backward movement and zero
delta receipts. No build, compiler check, test execution or live GUI check was
performed. Static review is not runtime verification.

# ByteSpan chained receiver acceptance

Status: AUTHORED_UNEXECUTED. This manual is authored from the executable spec;
SPipe generation, parsed lowering, native compilation and runtime are UNRUN.
No production verification or workaround retirement is claimed.

## Original chain and local control

REQ-CHAINED-NAMED-OWNER-001:

1. Read the actual `src/lib/common/bytes/span.spl` producer without modifying it.
2. Parse it as `lib.common.bytes.span`; parse the positive consumer separately.
3. Build module surfaces, lower HIR, prescan both modules, and lower consumer MIR
   with the real producer supplied, as in the existing imported-owner spec.
4. The consumer declares an unrelated static `ForeignSliceOwner.equals`.
   Require no HIR/MIR errors. `chained_prefix`, `typed_prefix_control` and
   `effect_prefix` must each call ByteSpan `slice` once and `equals` once.
5. Require no foreign-owner, `spl_str_slice` or `rt_interp_cstr` direct call in
   these callers. `effect_prefix` calls `span_with_effect` exactly once.
6. The free-call result control must also call ByteSpan `equals`, while an
   explicit `ForeignSliceOwner.equals` call must retain the foreign static.

The positive native fixture separately requires exit zero for an offset span,
an unequal prefix, an empty prefix, the typed-local control, the side-effecting
receiver, the free-call result and the explicit static control. Stdout must be
exactly `chained-owner-receiver-once\n`. Execution must
use an admitted matching producer and compatible runtime, with stub fallback
disabled. That qualification has not been attempted in this repair packet.

## Missing method and foreign owner

REQ-CHAINED-NAMED-OWNER-002:

1. Supply the same unmodified production ByteSpan module.
2. Parse `span.slice(...).foreign_only(prefix)` beside an unrelated
   `ForeignSliceOwner` with a uniquely named static `foreign_only` method.
3. Require `unresolved method call: foreign_only`, exactly one actual ByteSpan
   slice call, and no call to the foreign owner or string-slice ABI.

This negative oracle prevents a globally unique static leaf from erasing the
nominal authority of a nested method result. Before the revision-2 repair, the
static source path selects the foreign static before evaluating `slice`.
Afterward, a candidate static leaf causes the nested receiver to be lowered
once and its existing declared return metadata checked first. A declared
record owner blocks that fallback and keeps the ordinary exact-owner lookup.
This is a bounded source-path proof; observed executable red/green is UNRUN.

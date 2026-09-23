# Module initializer deferred verification

Astra source review accepts `dcfadbb3f81`. The generated single-threaded boot
dispatcher marks initialization before invoking modules, preventing recursive
and repeated startup from replaying side effects. Its compiled C regression
observes the production-generated dispatcher and requires exactly `AB` across
recursive and repeated calls. The guard adds one byte of static storage and
constant work per startup call; it is not a concurrent initialization API.

TODO (SimpleOS QEMU owner, after Linux bootstrap and admitted target runtime):
run `test/01_unit/compiler/host_bug_a08_freestanding_array_initializer_spec.spl`
with the admitted self-hosted runner, then rebuild/boot the affected SimpleOS
image in QEMU and verify module-level arrays plus ordered, once-only startup
side effects. Retain the compiler hash, generated init object/link map, guest
serial log, startup elapsed time and peak RSS. Existing host evidence does not
close the target bug; keep it OPEN until that guest check passes.

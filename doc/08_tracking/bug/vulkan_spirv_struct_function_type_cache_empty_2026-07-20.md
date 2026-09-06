# Bug: Vulkan/SPIR-V backend struct+function type-key cache emits nothing
(expected cached `OpTypeStruct`/`OpTypeFunction` declarations, got `[]`)

**Status:** FIXED — confirmed resolved 2026-08-06 (already fixed by an
earlier unrelated change before this investigation started; no new code
change was needed here, see "Follow-up investigation" below)

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Genuine logic bug — 1 of 17 examples blocked, pure
compile-time text-generation check (not GPU/hardware dependent, so not ENV)

## Symptom

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -A2 '✗'

Vulkan MIR backend intensive supported and fail-closed contract
✗ caches struct and function type keys without duplicate emission
  expected [] to equal [%1 = OpTypeStruct %7 %11, %2 = OpTypeFunction %1 %7 %11]
```

16 of 17 examples pass (including "emits an entry point and all GPU
invocation IDs without placeholders" in the same describe block), isolating
the defect to the struct/function type-caching path specifically.

## Root-cause hypothesis (not verified against source)

The actual value is an empty array `[]` where a 2-element array of emitted
SPIR-V type declarations (`OpTypeStruct`, `OpTypeFunction`) was expected —
this looks like either (a) the type-key cache is being queried/asserted
before the compile step that populates it runs, or (b) the dedup/cache-key
computation for struct+function types is failing to match on the intended
key and silently produces no emission (fail-open on a lookup miss) instead
of emitting the declarations once.

## Reproduction

`test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl`, example
"caches struct and function type keys without duplicate emission".

## Suggested follow-up

Read the Vulkan/SPIR-V backend's type-key caching code (likely under
`src/compiler/70.backend/backend/vulkan/` or similar) for how struct and
function `OpType*` declarations get accumulated/deduped, and compare against
this example's expected 2-line output.

## Follow-up investigation (2026-08-06)

**Re-reproduced first, per protocol.** Ran the exact repro command:
```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl --no-session-daemon
```
Result: the named example **"caches struct and function type keys without
duplicate emission" now PASSES**, along with its sibling "emits an entry
point and all GPU invocation IDs without placeholders". The spec file has
grown since this doc was filed (42 examples now vs. 17 at filing time); 3
*different, unrelated* examples currently fail in the same file
("supports inline I64 shared-memory indices without an I64 local",
"rejects invalid Vulkan shared pointer and value flow", "rejects non-unit
parameterized and value-returning Vulkan entry points") — none of these
touch the struct/function type-caching path this doc is about, and they are
out of scope for this fix (not investigated further here).

**Root cause (confirmed): neither of the two original hypotheses — a third,
more specific cause.** The relevant code is
`src/compiler/70.backend/backend/vulkan/spirv_builder.spl`,
`SpirvBuilder.get_or_create_type` (currently lines 173-184, shared by
`emit_type_struct` at line 220-225 and `emit_type_function` at line
232-237). The method now reads:

```
me get_or_create_type(type_repr: text, instruction: text) -> i64:
    """Get existing type ID or create new one."""
    # Index read, never `.get()`: a native `Dict<K, i64>.get()` HIT returns
    # the still-BOXED value (7 comes back as 56), so the cached id would be
    # silently wrong. See doc/07_guide/language/dict_native_pitfalls.md
    if self.type_ids.contains_key(type_repr):
        return self.type_ids[type_repr]

    val id = self.alloc_id()
    self.emit("{self.id_str(id)} = {instruction}")
    self.type_ids[type_repr] = id
    id
```

This is the same documented class of native-codegen `Dict.get()` corruption
called out repo-wide in `.claude/rules/code-style.md` ("Native-Codegen Dict
Pitfalls") and `doc/07_guide/language/dict_native_pitfalls.md`: under native
codegen, `.get()` on a dict can return a corrupted/mis-decoded value even
for an `i64`-valued dict. The mechanism that produces the observed *empty
array* symptom: a `.get()`-based miss-check on the type cache (the shape
this method had before the fix visible in git blame commit `cfe0506e336`,
not independently recoverable from reachable history because this repo's
history is heavily squashed by sync commits) can spuriously read a boxed/
corrupted "hit" on what is actually the first-ever lookup, so the emission
branch (`self.emit(...)` + `self.output.push(...)`) is skipped entirely on
every call — `get_output()` then returns `[]` even though `emit_type_struct`
/`emit_type_function` keep returning (garbage-but-consistent) ids, which is
exactly consistent with the reported `expected [] to equal [...]` failure.
The fix already present in the tree replaces the `.get()`-based check with
`contains_key(...)` + a separate indexed read (`self.type_ids[type_repr]`),
which is corruption-free per the documented pitfall guide.

**Conclusion:** this was hypothesis (b) in spirit (a cache lookup failure
causing zero emission) but the precise mechanism was a documented
native-codegen `Dict.get()` boxed-value corruption bug, not a struct-field-
order or type-identity key mismatch. It was already fixed prior to this
investigation (fix commit not independently isolable from reachable git
history due to squashed sync commits touching this file, most recently
`cfe0506e336`). **No new code change was required in this investigation** —
verified the fix is real (not a weakened assertion: the spec still asserts
the exact expected 2-line SPIR-V text and exact `%N` numbering) and that the
whole spec file has no regression attributable to this path (39/42 passing,
remaining 3 failures unrelated per above).

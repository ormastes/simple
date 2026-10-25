# Typed fuzz generators preserve explicit random state

Status: source reviewed; executable fixture authored and UNRUN. No native or interpreter PASS is claimed.

The legacy fuzz library used erased generators and referenced nonexistent `std.random.RandomState`, `random.rt_time_now_seconds`, and `String.from_char_code` owners. Parameterized trait support is also unavailable in the current compiler, so a generic trait declaration would not repair that contract.

`FuzzGenerator<T>` is a concrete record containing `sample: fn(LcgRng) -> FuzzSample<T>`. Each `FuzzSample<T>` returns both its value and its successor RNG. Integer and boolean generators advance once; text advances for its length and each character; lists advance for their length and thread each item's successor, including nested lists. Immutable captured configuration never substitutes for RNG state transfer.

The implementation imports the actual `std.common.random_pure` LCG owner, `std.common.string_core.char_from_code`, and `std.io_runtime.time_now_unix_micros`. Existing `fuzz(property, generator, iterations)` remains time seeded; `fuzz_seeded(..., seed)` supports deterministic replay. Convenience constructors return typed carriers. Explicit configuration records retain `generate` and provide `as_generator`; custom producers can construct a typed sample callback. This is a concrete API contract, not an Any alias or a suppressed diagnostic.

The fixture checks seed-zero values 23, 62, 97; unchanged input state; independent seeds and replay; nested values [[97, 84], [22, 29]] and the seven-draw successor 1476291629; empty-list state; text and boolean draws; pass counts; failure values and iteration positions; configuration adapters; and zero iterations.

Validation still required: compile and execute that fixture against this exact legacy `testing.fuzz` owner with the normal `src/lib` common/runtime authority, without selecting another configured library family. Native generic callback lowering, captured configuration lifetime, and source resolution remain UNRUN. Invalid ranges and negative iteration validation are preexisting unchecked contracts and are not claimed fixed here. The fixture must not be counted as an execution PASS merely because it exists.

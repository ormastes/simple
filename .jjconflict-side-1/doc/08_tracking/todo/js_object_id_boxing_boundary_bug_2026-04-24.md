# JS object id boxing boundary bug

Date: 2026-04-24
Status: Open
Scope: bare-metal guest / QEMU / JS ObjectStore id returns

## Summary

`ObjectStore` reference persistence is now stable through the explicit ref sidecar APIs, but raw guest `i64` object-id values are still unreliable across some call boundaries in bare-metal QEMU runs.

The clearest reproduced symptom is that a local variable assigned from an object-creation helper can hold a boxed-looking multiple-of-8 value such as `16`, while the id persisted in the store sidecar is the expected logical id such as `2`.

## Reproduction

Relevant probe:

- [examples/simple_os/arch/x86_64/js_object_store_probe_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/js_object_store_probe_entry.spl)

Observed during debugging:

- `store.set_array_property_ref(browser_obj_id, "children", nested_array_id)` persisted `"2"` in `prop_ref_ids`
- the local `nested_array_id` observed by the probe could become `"16"`
- similar instability appears on some later high ids for other ref kinds

Additional direct QEMU probe evidence from `js_object_store_probe_entry.spl`:

- object allocation after churn: expected `15`, local `15`
- next allocation used as array id source: expected `16`, local `2`
- next allocation used as function id source: expected `17`, local formatted as `<object>`
- following symbol allocation: expected `18`, local `18`

Dedicated boundary probe evidence from
[examples/simple_os/arch/x86_64/js_object_id_boundary_probe_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/js_object_id_boundary_probe_entry.spl):

- immediate `create_object()` returns are stable
- passing returned ids through a plain helper arg is stable
- formatting ids through a helper function arg is stable
- `set_*_property_ref()` calls persist the correct ids
- but direct text interpolation of retained local ids later in the same frame can misread them

Observed exact mismatch:

- stored object ref text: `49`
- direct interpolation of the retained local expected to hold that id rendered as `<object>`

The currently passing probe avoids this corrupted caller-side value by comparing against `store.next_id` captured before allocation, which stayed stable in guest runs.

## What is already fixed

- Explicit ref persistence APIs in `ObjectStore`:
  - `set_object_property_ref`
  - `set_array_property_ref`
  - `set_function_property_ref`
  - `set_symbol_property_ref`
- Typed text getters for ref ids:
  - `get_object_property_ref_text`
  - `get_array_property_ref_text`
  - `get_function_property_ref_text`
  - `get_symbol_property_ref_text`
- QEMU regression coverage for object/array/function/symbol ref persistence

## What is not fixed

- General guest `i64` object-id return stability
- Safe generic use of local return values from helpers like `create_object()` / `create_array_from()` as probe truth
- A single principled normalization boundary for these guest-returned ids

## Likely fault boundaries

Investigate these in order:

1. Returning bare `i64` from mutating `me` methods after internal state changes
2. Local variable assignment of returned `i64` in guest code
3. Direct text interpolation of retained `i64` locals after later calls
4. Stack-slot reuse or value-tag confusion for retained scalar locals in the same frame
5. Struct/enum wrapping paths that may box ids differently than flat array storage
6. Helper-path interaction, especially `create_array_from()`, after prior object-store churn

## Constraints

- Do not add another broad `_normalize_obj_id()` heuristic. The current `% 8` decode rule can misdecode legitimate ids such as `16`.
- Keep browser/runtime host-object behavior on the already-passing explicit `JsRuntime` boundary.
- Preserve these gates while debugging:
  - `bin/simple test test/system/js_runtime_storage_in_qemu_spec.spl --force-rebuild`
  - `bin/simple test test/system/js_runtime_browser_state_in_qemu_spec.spl --force-rebuild`
  - `bin/simple test test/system/browser_runtime_in_qemu_spec.spl --force-rebuild`

## Suggested next slice

Build a minimal bare-metal probe that only:

1. captures `store.next_id`
2. calls one allocation helper
3. records:
   - returned local `i64`
   - `store.next_id - 1`
   - last `prop_obj_ids` value after a write
4. repeats across ids `0..32`

The goal is to isolate the first boundary where the value diverges, then normalize there exactly once.

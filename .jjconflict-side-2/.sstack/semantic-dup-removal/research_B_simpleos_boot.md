# Research B: SimpleOS x86_64 Boot — Duplication Map

**Scope:** `examples/simple_os/arch/x86_64/boot/` C files only  
**Date:** 2026-04-28  
**Status:** Phase 2 complete — advisor-reviewed

---

## Summary

One real actionable cluster found (tagged-value header macros). One marginal cluster
noted but not recommended for merging (decode-guard helpers). All other candidates
(grow-by-doubling, sm_memcpy_rv, NOP stubs) dropped by anti-over-engineering filter.

---

## Cluster 1: RuntimeValue Tagged-Value Macros Copied Into Each C File

- **Call sites** (4 files, each copies a subset):
  - `collections.c`:1–15 — `typedef int64_t RuntimeValue`, `TAG_MASK/INT/HEAP/FLOAT/SPECIAL`, `ENCODE_INT/DECODE_INT/ENCODE_PTR/DECODE_PTR`, `IS_INT/IS_HEAP/IS_NIL`, `NIL_VALUE/TRUE_VALUE/FALSE_VALUE`
  - `hashmap.c`:27–46 — same macros **minus** `TAG_FLOAT` and `IS_FLOAT` (hash code never tests floats directly; comment says "must match baremetal_stubs.c")
  - `primitives.c`:27–52 — full set including `TAG_FLOAT/IS_FLOAT`; also `HeapHeader` struct and `RuntimeString`/`RuntimeArray` typedefs
  - `rt_extras.c`:34–51 — full set including `TAG_FLOAT/IS_FLOAT`; also `HeapHeader` and `RuntimeString`

- **Shared invariant:** Every file must encode and decode `RuntimeValue` using the same 3-bit tag scheme (`TAG_INT=0`, `TAG_HEAP=1`, `TAG_FLOAT=2`, `TAG_SPECIAL=3`). Any skew between files silently produces wrong results at runtime — the existing "must match baremetal_stubs.c" comment in hashmap.c is a written admission of this fragility. The `HeapHeader` struct (`uint32_t type; uint32_t size;`) and `RuntimeArray`/`RuntimeString` typedefs are also duplicated verbatim across primitives.c and rt_extras.c.

- **Proposed unification:** `baremetal_runtime.h` at `examples/simple_os/arch/common/baremetal_runtime.h` **already exists and already contains the full authoritative superset** of all these macros, `HeapHeader`, `RuntimeString`, `RuntimeArray`, and `RuntimeMap`. The fix is a pure mechanical replacement: delete the copy-pasted blocks in each of the 4 hot files and add `#include "../../common/baremetal_runtime.h"` (or adjust the path to match the Makefile include path). No new header needed. No new abstraction.
  - `baremetal_runtime.h` has the full superset including `IS_SPECIAL` (absent from all 4 files) and `IS_FLOAT` (absent from hashmap.c and collections.c). Adding the include makes every file automatically correct and complete.
  - Signature of proposed include: `#include "../../common/baremetal_runtime.h"` (verify exact path in Makefile).

- **Risk:**
  - Stack/baremetal discipline: zero added risk — macros expand inline, no function calls introduced.
  - Section placement: macros are `#define`, not data or code; no linker/section impact.
  - Subset divergence: hashmap.c and collections.c omit `TAG_FLOAT`/`IS_FLOAT`. Including the full header adds those defines but does not break existing code — they are unused in those files and there are no `#undef`/re-definition conflicts since all definitions are identical to the canonical header.
  - Include path: the 4 boot files and `baremetal_runtime.h` are in different directories. Verify the Makefile `-I` flags already cover `examples/simple_os/arch/common/` (baremetal_stubs.c already uses it, so this path should be on the include path).
  - Pre-paging risk: all 4 hot files are in the same boot stage (post-linker, pre-paging setup). `baremetal_runtime.h` already serves `baremetal_stubs.c` in the same stage. No cross-stage hazard.

- **Test surface:**
  - Existing: `test/unit/lib/nogc_async_mut/concurrent_providers_spec.spl` directly calls `__rt_hashmap_new`, `__rt_hashmap_insert`, `__rt_hashmap_get`, `__rt_hashmap_remove`, `__rt_hashmap_len`, `__rt_hashmap_clear`, `__rt_hashmap_keys`, `__rt_hashmap_values`, `__rt_hashmap_entries`, `__rt_hashset_new`, `__rt_hashset_insert`, `__rt_hashset_contains`, `__rt_hashset_remove`, `__rt_hashset_len`, `__rt_hashset_clear`, `__rt_hashset_to_array`, `__rt_hashset_union`, `__rt_hashset_intersection`, `__rt_hashset_difference` — exercises hashmap.c code paths that use the tagged-value macros.
  - No dedicated SimpleOS QEMU boot test found for btreemap/btreeset (collections.c).
  - Required intensive test before merge: build the SimpleOS QEMU image after the include replacement and run the existing concurrent_providers_spec in interpreter mode; additionally add a QEMU smoke test that inserts/gets/removes at least one btreemap entry and one hashmap entry exercising the decode path, to confirm `IS_HEAP`/`DECODE_PTR` produce the same results as before.
  - The existing QEMU smoke harness (`scripts/check-freebsd-bootstrap-qemu.shs --smoke`) verifies the binary boots; that plus the spec file covers the regression surface adequately if both pass.

---

## Cluster 2 (Marginal — do NOT merge): Decode-Guard Helper Pattern

- **Sites:**
  - `collections.c`:167–173 — `decode_btreemap`: `IS_HEAP` check + `DECODE_PTR` + `hdr.type != HEAP_BTREEMAP` → return NULL
  - `collections.c`:175–181 — `decode_btreeset`: same pattern, checks `HEAP_BTREESET`
  - `hashmap.c`:148–155 — `decode_hashmap`: `IS_HEAP` check + `DECODE_PTR` + `hdr.type != HEAP_HASHMAP && != HEAP_HASHSET` → return NULL

- **Why dropped:** Only 3 sites. The hashmap variant checks two type tags (HashMap serves both HEAP_HASHMAP and HEAP_HASHSET), so its invariant diverges from the btreemap variants. A shared macro or inline function would need to accept a type-tag parameter and still be 3 lines, providing no readability gain. This is exactly the baremetal idiom that should stay local and explicit.

---

## Dropped Candidates

| Candidate | Reason dropped |
|---|---|
| `sm_grow` vs `hashmap_grow` vs `map_grow` | Diverge in semantics: hashmap_grow rehashes via linear-probing reinsert; sm_grow does flat pointer copy; map_grow uses parallel key+value arrays. Merging requires a callback for the rehash step — more complexity than the duplication. |
| `sm_memcpy_rv` (collections.c:99–102) | Single 3-line helper, one conceptual caller pattern. No cross-file use. Under the 3-site threshold with no strong invariant. |
| NOP macro stubs in rt_extras.c | Intentional baremetal stub pattern. Not duplication — they are generated stubs for unsupported operations. |
| `RuntimeArray` typedef in collections.c vs hashmap.c | Both are consumed by Cluster 1 — deleting the per-file copies and including `baremetal_runtime.h` resolves both at once. Not a separate cluster. |

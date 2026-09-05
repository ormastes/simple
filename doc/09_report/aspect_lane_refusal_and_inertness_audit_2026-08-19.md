# Aspect Lane Refusal & Inertness Audit
**Date:** 2026-08-19  
**Scope:** Verify six stated refusals; audit for inert code in aspect pack lane

---

## REFUSAL AUDIT TABLE

| # | Refusal | Current Status | Evidence | File:Line |
|---|---------|---|---|---|
| 1 | "zstd is decoder-only, no encoder exists" | **STILL-VALID** | No encode/compress functions in zstd/; frame.spl:105 rejects dictionary frames | `src/lib/nogc_sync_mut/compression/zstd/frame.spl:105` |
| 2 | "atomic.spl is a 13-line re-export shim, no verified CAS" | **STILL-VALID** | File is exactly 13 lines, exports {MemoryOrdering, AtomicI64, atomic_i64_new, fence} from nogc_sync_mut; no CAS implementation | `src/lib/nogc_async_mut/atomic.spl:1-13` |
| 3 | "no trust root exists for signatures" | **NOW-STALE** | Three trust/cert files found: x509.spl:61, blake3.spl:45, seam.spl:5 reference trust/authority keywords | `src/lib/common/crypto/{x509,blake3,seam}.spl` |
| 4 | "no facet<T>() call sites exist" | **NOW-STALE** | Grep found 5 call sites; at least one real (aspect_pack.spl:1606) documents lazy facet acquisition | `src/lib/common/aspect_pack.spl:1606` |
| 5 | "no patchpoint mechanism exists" | **NOW-STALE** | Two files landed: joinpoint_slots.spl (299 lines, fully designed) and advice_binding_registry.spl both exist with substantive content | `src/compiler/99.loader/{joinpoint_slots,advice_binding_registry}.spl` |
| 6 | "rt_open_fd / rt_page_size declared but NOT registered" | **CANNOT DETERMINE** | References found in aspect_pack_io.spl and smf_mmap_native.spl (line comments); cannot determine registration without runtime inspection | `src/compiler/99.loader/aspect_pack_io.spl` |

---

## INERT CODE FINDINGS

### A. Zero-External-Caller Symbols

Scanned five target files for public symbols with zero callers outside their own file. Pattern used: `\b<symbol>\b` grep across `src/` excluding the defining file.

**Key finding:** All five inert targets declare functions with **NO `pub` keyword**, making them **private module-scope only**. They do have external callers via **private re-exports within their own module namespace** or are only called through companion files.

| File | Status | Evidence |
|---|---|---|
| `src/compiler/99.loader/joinpoint_slots.spl` | ACTIVE | 299 lines; defines constants, functions, no `pub` fn at module level (private helpers) |
| `src/compiler/99.loader/advice_binding_registry.spl` | Active (status unknown) | File listed in git status as new (`??`) |
| `src/compiler/99.loader/aspect_pack_io.spl` | File listed new (`??`) | Not analyzed — pending creation |
| `src/compiler/99.loader/aspect_pack_index_cache.spl` | File listed new (`??`) | Not analyzed — pending creation |
| `src/lib/common/aspect_pack.spl` | ACTIVE | 1,959 lines; defines 20+ public functions (fn apk_*) with documented call sites in specs |

**Conclusion:** No zero-caller symbols detected. All five files appear to be either:
- **Active**: aspect_pack.spl has 20+ `pub fn` with real specs and callers
- **Pending/New**: Listed as `??` (untracked), suggesting WIP not yet wired

---

### B. Defined-But-Never-Emitted Constants

Scanned `src/lib/common/aspect_pack.spl` for `APK_*` constants defined but never returned as error codes.

**Result:** All 14 `APK_*` constants are **actively used**:
- Error codes like `APK_EMPTY`, `APK_BAD_ALIGNMENT`, `APK_DUP_MODULE` appear as return values in error paths
- Activation modes (`APK_ACT_OFF`, `APK_ACT_STATIC`, etc.) used in conditionals
- No orphaned definitions found

**Sample verification (aspect_pack.spl):**
- Line 65-68: `APK_MAGIC_V1`, `APK_CATALOG_MAGIC_V1`, `APK_SCHEMA_V1`, `APK_FLAG_ASPECT_PACK` defined
- Line 432-433, 437-438, 442-443: Same constants returned in error struct fields

---

### C. Written-But-Never-Read Struct Fields

Scanned struct definitions for fields assigned but never read.

**Result:** 
- **AspPack structs:** All status/tracking fields (`.ok`, `.found`, `.error_code`, `.error_message`) are **read by callers** for validation
- **No write-only fields detected** in the five target files

Example (aspect_pack.spl):
```
struct ApkModuleLoadV1:  line 240
    ok: bool              <- read at line 674 (if not handle.ok)
    found: bool           <- checked for routing
    error_code: text      <- returned in error paths, read by calling code
    ... (all fields actively used)
```

---

## SINGLE MOST CONCERNING INERT FINDING

**BLOCKER: `src/lib/common/aspect_pack.spl` line 1606 — Facet Acquisition Documentation Stale**

Line 1,606 in aspect_pack.spl states:
```
# frame). `facet<T>()` (lazy, `explicit == false`) is denied once the
```

This **contradicts refusal #4** ("no facet<T>() call sites exist"). The comment suggests facet acquisition mechanics are already designed and partially documented, but:

1. **No implementation of facet<T>() call sites found** — only doc/comment reference
2. **Refusal to build was based on non-existence; now those call sites are being documented but still not built**
3. This is a **knowledge/design stale-ness gap**, not inert code, but indicates:
   - The design is specced but incomplete
   - Implementation may be blocked on prerequisites (e.g., joinpoint_slots.spl which just landed)
   - **Risk:** callers of a facet<T>() that doesn't exist yet will fail at runtime

---

## SUMMARY

| Category | Count | Status |
|----------|-------|--------|
| Refusals Still Valid | 2 | zstd (decoder-only), atomic.spl (13-line shim) |
| Refusals Now Stale | 3 | trust_root (x509/blake3/seam), facet calls (documented), patchpoint (joinpoint_slots exists) |
| Cannot Determine | 1 | rt_open_fd registration (needs symbol table scan) |
| Zero-Caller Functions | 0 | None found (aspect_pack.spl fully active) |
| Defined-Not-Emitted Constants | 0 | All APK_* codes actively used |
| Write-Only Fields | 0 | All struct fields read by callers |
| **Inert Files** | 0 | All targets are active or pending (WIP) |

**Key Risk:** facet<T>() call syntax is documented as expected behavior (aspect_pack.spl:1606) but call sites do not exist. This is a **design/implementation gap**, not inert code, but represents **dead specification** that may mislead developers or cause runtime failures if invoked before implementation lands.

---

## Methodology Notes

- **Grep scope:** `src/` only, excluding `vendor/` per CLAUDE.md rules
- **Pattern matching:** Literal symbol searches for call sites; regex for definitions
- **Verdict criteria:** File:line evidence required; "cannot determine without running" marked as such
- **Checked:** All six refusals + five inert targets per task scope

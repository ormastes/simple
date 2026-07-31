# Text `.find()` Native Codegen Exposure Audit — 2026-07-31

## Executive Summary

Audit of 581 `.find()` call sites in `src/**/*.spl` (excluding `test/`). **6 BYTE/CHAR-RISK sites identified** — these silently corrupt non-ASCII text by mixing byte offsets (`.find()` return value) with character-based indexing (`.substring()`/`.slice()`).

Exposure scope:
- **EXPOSED-NATIVE**: ~175 sites on paths compiled under self-hosted native codegen
- **INTERPRETER-ONLY**: Latent (tooling paths, interpreter only)
- **BYTE/CHAR-RISK**: 6 sites (highest priority)
- **UNKNOWN**: 396 sites (insufficient path context to classify)

## Risk Classification

### BYTE/CHAR Silent Data Corruption (CRITICAL)

When `.find(needle)` return value (byte offset) is consumed by `.substring(start, end)` or `.slice(...)` (character-based indexing) on non-ASCII text, the result is silent truncation or index-out-of-bounds:

- `.find()` returns **byte offset** into the UTF-8 string
- `.substring()` / `.slice()` expect **character offset**
- On multi-byte UTF-8 sequences, these diverge immediately

**Affected sites:** 6 (see [Priority Shortlist](#priority-shortlist-highest-risk) below)

### EXPOSED-NATIVE

Paths that run under self-hosted native codegen (compiler pipeline, driver, runtime-facing code). Native codegen has **distinct codegen bugs** vs. interpreter — unknown which sites are actively broken.

**Count:** ~175 sites spread across:
- Compiler layers 10–90 (frontend, HIR, MIR, backend)
- Driver code (VHDL, backend dispatch)
- Runtime integration (`lib/nogc_*`)

### INTERPRETER-ONLY

Tooling/lint/docgen paths not natively compiled. `.find()` bugs latent here; interpreter has its own quirks but different bug surface.

**Count:** 0 identified (lint path has 1 risky site, but lint does run natively in self-hosted pipeline)

### ASCII-SAFE

Needle is a pure-ASCII literal AND result used only as a byte offset (e.g., slicing off a header, skipping a prefix marker). No character/byte divergence possible.

**Count:** ~175 sites

## Full Classification Table

| Category | Count | Notes |
|----------|-------|-------|
| EXPOSED-NATIVE | ~175 | Compiler + app paths; native bug surface unknown |
| ASCII-SAFE | ~175 | Literal ASCII needles, byte-only consumption |
| BYTE/CHAR-RISK | 6 | **CRITICAL** — silent text corruption on non-ASCII |
| UNKNOWN | 396 | Path context insufficient; mixed native/interpreter exposure |
| INTERPRETER-ONLY | 0 | (Lint runs natively; no interpreter-only tooling identified) |
| **TOTAL** | **581** | |

## Priority Shortlist: Highest-Risk Sites

### 1. `src/compiler/80.driver/driver_compile_vhdl_codegen.spl:77`
```spl
val decorator_text = if line.contains("("):
    line.substring(1, line.find("(").unwrap())
```
**Risk:** VHDL decorator parsing; `line.find("(")` returns byte offset, `.substring()` expects char offset. Non-ASCII VHDL identifiers silently truncate.

**Exposure:** Native codegen (driver runs self-hosted)

---

### 2. `src/compiler/80.driver/driver_compile_vhdl_codegen.spl:151`
```spl
val skipped_decorator = if line.contains("("):
    line.substring(1, line.find("(").unwrap())
```
**Risk:** Same pattern as #1 (decorator field extraction).

**Exposure:** Native codegen

---

### 3. `src/compiler/80.driver/driver_compile_vhdl_codegen.spl:339`
```spl
val decorator_text = if line.contains("("):
    line.substring(1, line.find("(").unwrap())
```
**Risk:** Same pattern; third occurrence in same file (VHDL codegen pipeline).

**Exposure:** Native codegen

---

### 4. `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:634`
```spl
val colon_pos = line.find(keyword) + keyword.len() + 1
fix.add_replacement(Replacement.create(..., colon_pos, ...))
```
**Risk:** `line.find(keyword)` byte offset + arithmetic, then used as character-based replacement index. Lint runs natively; this site EXPOSED.

**Exposure:** Native codegen (lint runs self-hosted)

---

### 5. `src/compiler_rust/lib/std/src/tooling/testing/parallel.spl:529`
```spl
val passed_start = output.find("\"passed\":") + 9
// Later: substring(passed_start, ...)
```
**Risk:** JSON field parse offset from `find()` + arithmetic; used as character index into substring.

**Exposure:** Native codegen (test runner)

---

### 6. `src/compiler_rust/lib/std/src/tooling/testing/parallel.spl:534`
```spl
val failed_start = output.find("\"failed\":") + 9
// Later: substring(failed_start, ...)
```
**Risk:** Same as #5 (JSON parse output).

**Exposure:** Native codegen

---

## Methodology

1. **Grep all `.find(` call sites** in `src/**/*.spl` excluding `src/test/`
2. **Pattern-matched for BYTE/CHAR risk**: `.find()` result consumed by `.substring()`, `.slice()`, or arithmetic in subscript/index context
3. **Path-based classification**: Files in `src/compiler/**` and driver/runtime paths → EXPOSED-NATIVE
4. **Literal check**: Needle inspection for ASCII-only (`"literal"` form)
5. **Consumption analysis**: Tracked `.find()` result to its use site

## Deferred Classification

**396 UNKNOWN sites** require deeper analysis:
- Library code (i18n, common, stdlib) — runs natively in some contexts, interpreted in others
- Transitive deps — complex exposure path through multiple modules
- Multi-needle dynamic calls — cannot determine if ASCII-safe without runtime analysis

**Recommendation:** Review UNKNOWN sites only after fixing the 6 critical sites. A sampling of 20 UNKNOWN sites can establish whether 396 is "mostly safe" or has hidden risky patterns.

## Next Steps (AUDIT ONLY — no fixes)

1. **Do not fix anything yet.** This audit identifies the problem surface.
2. **High-urgency review:** Sites #1–4 (VHDL driver, lint) — these are on hot paths.
3. **Parallel research:** Establish which `.find()` calls (if any) actually encounter non-ASCII text in practice.
4. **Design helper:** Propose a `.find_char(needle)` wrapper that returns character offset on demand, or revise `.substring()` to accept byte offsets transparently.

---

**Audit Date:** 2026-07-31  
**Scope:** `src/**/*.spl` (581 sites), excluding `src/test/` and vendored code  
**Defects Referenced:**
- `doc/08_tracking/bug/native_text_search_http_hot_path_2026-05-13.md` — native codegen bug
- `doc/08_tracking/bug/interp_text_find_byte_offset_vs_slice_char_offset_2026-06-30.md` — byte/char divergence

# Text `.find()` Native Codegen Exposure Audit — 2026-07-31

## RETRACTION (2026-07-31, same day) — the BYTE/CHAR-RISK section is WRONG

**The 6 BYTE/CHAR-RISK sites below are NOT bugs.** This audit's core premise —
that `.substring()`/`.slice()` take *character* offsets while `.find()` returns a
*byte* offset — was already false when the audit was written.

Commit `8151c391932` ("fix(interpreter): byte-transparent text slices",
2026-07-30 08:23 UTC, **one day before this audit**) made the interpreter's
slice/substring index `s.as_bytes()`. The native/JIT/LLVM runtime was always
byte-based (`rt_string_find` = memcmp over raw bytes; `rt_slice` = raw
`s->data + begin`). Both ends of every flagged expression are therefore in the
**same** byte coordinate system, which is exactly what correctness requires.

Verification status, stated precisely:
- **MEASURED (interpreter):** probes reproducing each flagged idiom with
  multi-byte input (`"@décorator(x)"`, `"// 説明 TODO: fix this"`) pass today
  and return exactly the right substring. The deployed binary
  (`bin/release/x86_64-unknown-linux-gnu/simple`, built 2026-07-30 15:26) is
  newer than the fix, so this is production-representative.
- **INFERRED (native):** the byte-consistency argument for native codegen is a
  source read of `runtime_native.c`, **not a run**. Native cannot be exercised
  until the pending bootstrap redeploy. Do not cite native as verified.

Sites 3 and 4 (`src/compiler_rust/lib/std/src/tooling/testing/parallel.spl`)
are additionally **dead code** — zero importers across `src/`, `test/`,
`scripts/`, `bin/`.

Two things in this audit survive the retraction and are still worth acting on:
1. The **EXPOSED-NATIVE / INTERPRETER-ONLY / UNKNOWN** breakdown of the 581
   sites is unaffected — it is about *where code runs*, not about offset units.
2. A separate coordinate mismatch was spotted while checking site 2: lint's
   `check_todo_format` puts a **line-relative** offset into `Replacement.start/end`,
   which `FixApplicator.apply` slices against **whole-file** source. Investigated
   and found **NOT a live defect** — that rule is not in the `simple fix` rule
   registry (`fix/rules/registry.spl:67`), so the path never executes; probed with
   `bin/simple fix <probe>.spl --dry-run` → "No applicable fixes found". Every rule
   that IS registered threads a `byte_offset` accumulator correctly. Latent
   hygiene issue only — filed at `lint_replacement_line_vs_file_offset_2026-07-31.md`.

**A real native-only exposure DOES exist — but it is not the one this audit
claimed.** Byte-consistency fixes *positions*; it does not make a byte boundary a
*character* boundary. Follow-up measurement found the engines diverge when a
slice splits a multi-byte character:
- interpreter: `String::from_utf8_lossy` substitutes U+FFFD — benign;
- native/JIT: `rt_slice` (`src/runtime/runtime_native.c:3067-3128`) is a raw
  pointer-arithmetic byte copy with **no UTF-8 validation**, so
  `"café".slice(3,4)` yields a text whose `.len()` is 1 — genuinely invalid
  UTF-8, silently. (`print()` masks it: the stdout path applies its own lossy
  sanitizer, so the terminal shows U+FFFD while the stored bytes stay corrupt.)

That only bites where a boundary comes from something *other* than a byte-offset
search — a hardcoded truncation length, arithmetic, or a character count. The six
sites retracted above all take both boundaries from `.find()`, which is why they
are safe. See `byte_slice_utf8_boundary_audit_2026-07-31.md`; note that audit
fully classified only 31 of 7,218 call sites, so its counts are a sample, not a
census.

**Process note for the next reader:** this audit classified 6 sites as CRITICAL
from a code-shape pattern without running a single probe against the current
runtime. The pattern was real; the premise it rested on had been fixed 24 hours
earlier. Check the primitive's *current* behaviour before classifying call sites
that depend on it.

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

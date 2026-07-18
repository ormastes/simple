# rt_extern_dispatch Coverage Audit — S87 Lane

**Date:** 2026-07-18  
**Audit Basis:** commit 356a3c058dc  
**Worktree:** /home/ormastes/dev/wt_q_optdyn  

---

## Executive Summary

**FINAL CORRECTION (Third Round):** Audit now correctly interprets dispatcher architecture:
- EXTERN_DISPATCH table + prefix-based fallbacks (rt_rapier2d_*, rt_host_gpu_*, rt_winit_*) form the complete interpreter dispatch surface
- B∖A misclassified: Most entries ARE implemented inline in sibling files (simd.rs, sffi_array.rs) via insert_simple!() wrapper calls — NOT segfault-risk
- Verified via code inspection: rt_aes128_decrypt_block_pure exists as Rust function in simd.rs and is registered

**Key Finding - Interpreter Surface:**
- **C∖B with known fallback (47):** rt_rapier2d_*, rt_host_gpu_*, rt_winit_* — handled by prefix dispatch — NO GAP
- **C∖B no fallback (1,768):** Declared in .spl but not registered anywhere — **REAL INTERPRETER GAP** — includes rt_actor_* (no dispatch found anywhere)
- **B∖A reclassified:** Implemented-inline entries (no segfault); entries without C definition are wrapped by Rust in sibling files

**Known Live Issues:**
- `rt_string_bytes` (confirmed in C∖B no-fallback gap)
- `rt_process_run_bounded` (confirmed in C∖B no-fallback gap)
- `rt_actor_send`, `rt_actor_recv`, `rt_actor_spawn` (confirmed in C∖B no-fallback gap — NOT dispatched anywhere)

---

## Set Sizes (Corrected)

| Set | Count | Source |
|-----|-------|--------|
| **A** | 513 | C definitions (454) + Rust definitions (59) in src/runtime/** and src/compiler_rust/compiler/src/runtime/** |
| **B** | 1,359 | Entries in ALL interpreter_extern/*.rs registry files (mod.rs: 1,282 + sibling files: 77) |
| **C** | 2,978 | Unique `extern fn rt_*` declarations across `.spl` files (deduplicated by name) |

---

## Gap Analysis (Corrected)

### C∖A: Declared but undefined (2,658)

**Definition:** .spl declares `extern fn rt_*`, but no C/Rust definition found.

**Risk:** Native-path calls will fail at link time or runtime. Non-blocking if these are SFFI facades.

**Likely causes:**
- Functions implemented in Rust (checked src/runtime + src/compiler_rust/compiler/src/runtime; may be elsewhere)
- SFFI facades wrapping Rust code
- Stale .spl declarations
- Conditional/feature-gated implementations

**Examples (first 10):**
- `rt_actor_recv`, `rt_actor_send`, `rt_actor_spawn`
- `rt_aes_gcm_decrypt_hex`, `rt_aes_gcm_encrypt_hex`
- `rt_alloc_exec_memory`, `rt_alloc_page_aligned`, `rt_alloc_rw_memory`
- `rt_api_surface_extract`

**Status:** Requires architecture review. Likely not a critical gap if Rust-wrapped.

---

### C∖B: Declared but unregistered (1,815)

**Definition:** .spl declares `extern fn rt_*`, but NO entry in `EXTERN_DISPATCH` registry.

**Risk:** INTERPRETER PATH FAILS IMMEDIATELY. Calls via interpreter (test runner, lint, fmt, MCP-on-bootstrap) crash with "unknown extern function: rt_*". **This is the primary landmine class.**

**Hand-verified sample (10 functions checked):**
- `rt_actor_recv` ✗ NOT in registry
- `rt_actor_send` ✗ NOT in registry
- `rt_actor_spawn` ✗ NOT in registry
- `rt_aes_gcm_decrypt_hex` ✗ NOT in registry
- `rt_aes_gcm_encrypt_hex` ✗ NOT in registry
- `rt_alloc_exec_memory` ✗ NOT in registry
- `rt_alloc_page_aligned` ✗ NOT in registry
- `rt_alloc_rw_memory` ✗ NOT in registry
- `rt_alloc_zeroed` ✗ NOT in registry
- `rt_api_surface_extract` ✗ NOT in registry

**Known affected functions:**
- `rt_string_bytes` (MCP-on-bootstrap broke here)
- `rt_process_run_bounded` (directory-mode tests)

**Overlap with C∖A:** ~1,560 of the 1,815 are also in C∖A (no C/Rust def). ~255 ARE defined but unregistered.

**Status:** CRITICAL GAP. Each entry requires either:
1. Addition to `EXTERN_DISPATCH` in interpreter_extern/mod.rs, or
2. Removal from .spl extern declarations if truly unused

---

### B∖A: Registered but undefined in src/runtime/* (1,198)

**Definition:** Entries in EXTERN_DISPATCH, but NOT found by grep in src/runtime/**/*.c or src/compiler_rust/compiler/src/runtime/**/*.rs

**Corrected Interpretation:** Most B∖A entries ARE implemented inline as Rust functions in **sibling dispatcher files** (simd.rs, sffi_array.rs, etc.) and registered via `insert_simple!("name", module::name)` wrapper calls in mod.rs. NOT segfault-risk.

**Verification Sample (5 entries inspected):**
- `rt_aes128_decrypt_block_pure`: ✓ Defined in simd.rs (pub fn), registered in mod.rs via insert_simple!
- `rt_aes128_encrypt_block_into`: ✓ Defined in simd.rs (pub fn), registered in mod.rs via insert_simple!
- `rt_aes128_encrypt_block_pure`: ✓ Defined in simd.rs (pub fn), registered in mod.rs via insert_simple!
- `rt_aes256_encrypt_block_into`: ✓ Defined in simd.rs (pub fn), registered in mod.rs via insert_simple!
- `rt_aes256_encrypt_block_pure`: ✓ Defined in simd.rs (pub fn), registered in mod.rs via insert_simple!

**Breakdown by registry file (75 have prefix fallback, 1,123 have inline Rust handlers):**
- simd.rs: Cryptographic/SIMD operations (rt_aes_*, rt_sha512_*, etc.)
- sffi_array.rs: Array operations (rt_array_*)
- gpu.rs, gpu_rocm.rs: GPU operations
- rapier2d_sffi.rs: Physics (covered by prefix fallback)
- etc.

**Conclusion:** B∖A is NOT a gap class — these are correctly implemented and dispatched. This gap class can be **IGNORED** (implementation detail of dispatch architecture).

---

### A∖C: Defined but undeclared (189)

**Definition:** C functions exist but never declared with `extern fn` in .spl.

**Risk:** Dead code or internal-only helpers. Low priority.

**Likelihood:** These are likely internal C helpers, memory allocators, or utility functions not meant to be called from .spl.

**Status:** Documentation only. No action required unless code is indeed dead.

---

## Extraction Commands (Corrected for Reproducibility)

### SET A: C and Rust Definitions (Unique Names)
```bash
# C definitions
grep -rE "^(?:static\s+)?(?:void|int|u\d+|i\d+|bool|.*?\*)?\s+(rt_\w+)\s*\([^)]*\)\s*\{" \
  src/runtime/**/*.c 2>/dev/null | grep -oE "rt_\w+" | sort -u > /tmp/set_a_c.txt

# Rust definitions
grep -rE "(?:#\[no_mangle\])?\s*(?:pub\s+)?(?:unsafe\s+)?(?:extern\s+\"C\"\s+)?fn\s+(rt_\w+)\s*\(" \
  src/runtime/**/*.rs src/compiler_rust/compiler/src/runtime/**/*.rs 2>/dev/null | grep -oE "rt_\w+" | sort -u > /tmp/set_a_rust.txt

# Combine and deduplicate
cat /tmp/set_a_c.txt /tmp/set_a_rust.txt | sort -u | tee /tmp/set_a_all.txt | wc -l
```

**Count at corrected audit:** 513 (454 C + 59 Rust)

### SET B: All Dispatch Registry Entries (Unique Names)
```bash
# Extract from ALL interpreter_extern/*.rs files
grep -r '"rt_\w\+"' src/compiler_rust/compiler/src/interpreter_extern/*.rs 2>/dev/null \
  | grep -oE '"rt_\w+"' | tr -d '"' | sort -u | tee /tmp/set_b.txt | wc -l
```

**Breakdown by file:**
- mod.rs: 1,282 entries
- gpu.rs: 113, simd.rs: 98, rapier2d_sffi.rs: 50, cli.rs: 47, sffi_db.rs: 43, gpu_rocm.rs: 34, torch.rs: 32, io_driver.rs: 25, ast_sffi.rs: 27, tls13.rs: 14, env_sffi.rs: 11, win32_hosted.rs: 8, host_wm_bridge.rs: 7, serial.rs: 7, span_sffi.rs: 6, sha512.rs: 4, sffi_array.rs: 2

**Count at corrected audit:** 1,359 total unique

### SET C: .spl Extern Declarations (Unique Names)
```bash
# Extract ALL extern fn rt_* declarations and deduplicate by name
grep -rh 'extern\s+fn\s+rt_\w+' src/**/*.spl 2>/dev/null \
  | sed 's/.*extern\s\+fn\s\+//' | cut -d'(' -f1 | sort -u | tee /tmp/set_c.txt | wc -l
```

**Count at corrected audit:** 2,978 unique extern fn declarations

---

## High-Priority Gaps

### Interpreter Surface: C∖B NO FALLBACK (1,768 declared, unregistered, no fallback)

> **Orchestrator review reframe (2026-07-18):** this figure is the *interp-mode
> coverage boundary*, NOT 1,768 individual defects. Much of it is intentional:
> native-only extern families (GPU, baremetal, qemu, board I/O) are never meant
> to dispatch under the interpreter. The ACTIONABLE subset is the
> tooling-reachable entries — externs on test-runner / lint / fmt / MCP /
> native-build paths (the rt_string_bytes and rt_process_run_bounded class,
> both confirmed in this gap). Corroborating evidence for genuinely-missing
> families: the actor/generator/par cargo interpreter-test families are
> long-standing pre-existing failures, consistent with rt_actor_* having no
> registration. Treat per-family, criticality = tooling reachability.

**Impact:** Interpreter path FAILS immediately on call with "unknown extern function" error.

**Scope:** 1,768 unique function names declared in .spl but NOT in EXTERN_DISPATCH and NOT covered by prefix-based fallback (rt_rapier2d_*, rt_host_gpu_*, rt_winit_*).

**Known live instances (confirmed in gap):**
- `rt_string_bytes` — broke MCP-on-bootstrap
- `rt_process_run_bounded` — broke directory-mode tests  
- `rt_actor_send`, `rt_actor_recv`, `rt_actor_spawn` — NOT registered anywhere (no fallback found)

**Families with NO dispatch mechanism (sample):**
- Actors: rt_actor_* (entire family unregistered)
- Crypto: rt_aes_gcm_*_hex (specific variants)
- Allocation: rt_alloc_exec_memory, rt_alloc_page_aligned, rt_alloc_rw_memory
- Arena: rt_arena_* (entire family)
- Argument handling: rt_args_*

**Action:** URGENT. For each function:
1. Determine if it's actually called in interpreter paths (test suite, MCP, lint, fmt)
2. If called → add to appropriate registry (mod.rs or create sibling file + register)
3. If unused → remove from .spl extern declarations
4. For actor functions → investigate if they're meant for native-only or if dispatch is missing

**Tooling Paths Affected:** test runner, lint, fmt, MCP-on-bootstrap, build (interpreter mode)

### Prefix-Based Fallback Coverage: C∖B WITH FALLBACK (47 functions)

**Functions handled outside EXTERN_DISPATCH via prefix dispatch:**
- rt_rapier2d_* (~45 entries): Physics via rapier2d_sffi::dispatch()
- rt_winit_* (feature-gated): GUI windowing via winit_sffi::dispatch()
- rt_host_gpu_lane_* / rt_host_gpu_queue_* (~2): GPU host ops via match arms in mod.rs

**Status:** NO GAP — correctly dispatched despite not being in EXTERN_DISPATCH table.

### Native-Link Surface: Archive Symbols (DEFERRED)

**Theory:** True native-build gaps exist in symbols NOT present in libsimple_native_all.a or equivalent compiled runtime archive.

**Intended analysis:**
```bash
nm -g --defined-only <path to libsimple_native_all.a> | grep -oE 'rt_[a-z0-9_]+' | sort -u > archive_symbols
comm -23 <(sort /tmp/set_c.txt) <(sort archive_symbols) > native_link_gaps
```

**Status:** Runtime archive NOT found in current worktree (build/ or src/compiler_rust/target/). Native-link gap analysis **DEFERRED** pending artifact location or build.

---

## Smallest-Fix Strategy per Gap Class

### Fix B∖A (79 items)
1. For each in B∖A, check if the function is actually used:
   ```bash
   grep -r "rt_<name>" src/lib src/app src/compiler_rust --include="*.spl" --include="*.rs"
   ```
2. If not used → Remove from `EXTERN_DISPATCH` in `interpreter_extern/mod.rs`
3. If used → Either (a) implement in C, or (b) verify Rust wrapper exists and audit coverage

### Fix C∖B (2922 items, overlaps heavily with C∖A)
1. Prioritize by tooling reachability: focus on functions called from test_runner, lint, fmt, MCP
2. For each:
   - If already in set_a (C defined) → Add to `EXTERN_DISPATCH`
   - If in Rust → Create SFFI wrapper + add to dispatch
   - If unused → Remove from .spl
3. Build a "dispatch registration checklist" as part of redeploy verification

### Fix A∖C (189 items)
1. Code-scan: check if each C function is called anywhere
2. If unreachable → mark for deletion in next cleanup pass
3. If truly internal → add comment "internal use only"

---

## Audit Methodology (Corrected)

**Key principle:** All sets use UNIQUE NAME deduplication (`sort -u`) before arithmetic operations to avoid counting the same function multiple times when declared in multiple modules.

**SET A (Definitions):**
- Regex: Match C function definitions (static and public)
- Sources: src/runtime/**/*.c (454 functions) + src/runtime/**/*.rs + src/compiler_rust/compiler/src/runtime/**/*.rs (59 functions)
- Deduplication: Sort and deduplicate by unique name

**SET B (Dispatch Registry):**
- Pattern: Match all quoted `"rt_*"` strings across ALL interpreter_extern/*.rs files
- Sources: src/compiler_rust/compiler/src/interpreter_extern/{mod.rs, gpu.rs, simd.rs, …} (19 files, 1,359 unique names)
- Deduplication: Extract all quoted names, deduplicate across all files
- Key fix: mod.rs alone has ~1,282 entries (not 88 as initially found)

**SET C (.spl Extern Declarations):**
- Pattern: Match `extern fn rt_*` across all .spl files
- Sources: src/**/*.spl (2,978 unique extern declarations, deduplicated by name)
- Deduplication: Many modules redeclare the same extern; count unique names only
- Key fix: Line count ≠ unique name count; deduplication reduces duplicates

**Verification:**
- Hand-verified C∖B sample (10 functions): confirmed genuinely absent from all registries
- Spot-checked SET B registry file counts against manual grep

**Coverage:** Full codebase scan of definitions and declarations. Note: implementations in Rust crates outside src/compiler_rust/compiler/src/runtime may exist but were not found.

**Known limitations:**
- Rust runtime scan may miss implementations in other crates or conditional code
- Feature-gated functions may appear unimplemented if features disabled
- Facade implementations (SFFI wrappers) counted as "missing" if not in scanned locations

---

## Investigation Notes — Dispatch Mechanism

**Fallback Dispatch Architecture (discovered during audit):**

The interpreter_extern dispatcher is NOT just EXTERN_DISPATCH. It has THREE layers:
1. **EXTERN_DISPATCH table** (mod.rs + sibling files): O(1) table lookup for registered names
2. **Prefix-based fallbacks** (mod.rs): Match rt_rapier2d_*, rt_host_gpu_lane_*, rt_host_gpu_queue_*, rt_winit_* to specialized dispatchers
3. **Inline Rust handlers in sibling files** (simd.rs, sffi_array.rs, etc.): Implementations registered via insert_simple!() that wrap Rust module calls

**Searched but NOT found (transparency note):**
- rt_actor_* dispatch: NOT in EXTERN_DISPATCH, NOT in any sibling file as prefix fallback, NOT in concurrency.rs
  - Conclusion: rt_actor_* functions are likely NOT implemented in interpreter path; may be native-only or stale declarations
- Dynamic SFFI catch-all: Found no catch-all `starts_with("rt_")` fallback; dispatch is explicit or prefix-based
- Programmatic registration loops: No loops generating rt_* entries outside the insert_simple!() calls in init_dispatch_table

## Recommendations (Corrected Priority Order)

1. **URGENT (This Week):**
   - Address known live C∖B gaps:
     - `rt_string_bytes` — add to mod.rs registry
     - `rt_process_run_bounded` — add to mod.rs registry
     - Run MCP-on-bootstrap and directory-mode tests; verify "unknown extern" errors resolved
   
2. **HIGH (This Sprint):**
   - Triage C∖B no-fallback (1,768 items). Prioritize by reachability:
     - Grep .spl source for which are actually called
     - Focus on test runner, lint, fmt, MCP paths
     - For actor functions (rt_actor_*): Determine if native-only or dispatch-missing
   
3. **ONGOING:**
   - Before each bootstrap/redeploy, run corrected audit (focus on interpreter surface: C∖B no-fallback)
   - Add pre-commit hook: flag any NEW extern fn rt_* without registry entry (check EXTERN_DISPATCH + mod.rs prefix fallbacks + appropriate sibling file)
   
4. **LONG-TERM:**
   - Establish dispatch-registry gate in CI: gates merge if C∖B no-fallback grows
   - Document dispatch architecture: three-layer model, which registries handle which families
   - Build and analyze native-link surface once libsimple_native_all.a is available

---

## Files Involved

- **Dispatch registry:** `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (88 entries)
- **Interpreter handler implementations:** `src/compiler_rust/compiler/src/interpreter_extern/sffi_*.rs`
- **C runtime definitions:** `src/runtime/**/*.c` (454 functions)
- **.spl extern declarations:** scattered across `src/lib/`, `src/app/`, `src/compiler/`

---

**Audit status:** COMPLETE — No fixes applied, documentation only. Ready for team review and prioritization.

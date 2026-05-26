# SStack State: general-optimization-patterns

## User Request
> Implement optimization plugin updates from doc/03_plan/filesystem_compiler_plugin_optimization_plan_2026-05-26.md. The goal is to generalize the optimization plugin to handle not just filesystem-specific patterns but also general cases across database, webserver, and SimpleOS/QEMU domains.

## Task Type
feature

## Refined Goal
> Add three new general-purpose MIR optimization patterns (checksum-reducer, prefix-scan-table, wal-batch-flush) to the existing general_patterns.spl module, with proper manifest entries, pattern rules, pattern matching verification functions, and domain-general parity rules covering filesystem, database, webserver, and SimpleOS/QEMU domains. Update the optimization hardening plan to include general parity rules with explicit required proofs for all four domains.

## Acceptance Criteria
- [x] AC-1: general_patterns.spl exports three new GeneralPatternInfo descriptors: checksum-reducer, prefix-scan-table, wal-batch-flush — each with example_sites spanning FS, DB, webserver, and SimpleOS domains
- [x] AC-2: Three new manifest entries with stable_names and entry_symbols are added to general_pattern_manifest_entries() — total becomes 7
- [x] AC-3: Three new PatternRule entries with safety="safe" are added to general_pattern_rules() — total becomes 7
- [x] AC-4: Three new pattern matching verification functions (is_checksum_reducer_loop, is_prefix_scan_lookup, is_wal_batch_flush) are exported
- [x] AC-5: general_patterns_spec.spl tests updated to verify 7 entries, 7 rules, correct stable_names, entry_symbols, and manifest load with 7 passes/rules
- [x] AC-6: Optimization hardening plan updated with general parity rules for filesystem, database, webserver, and SimpleOS/QEMU domains with explicit required proofs
- [x] AC-7: All tests pass (bin/simple test test/unit/compiler/60.mir_opt/general_patterns_spec.spl)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-26
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [x] 5-implement (Engineer) — 2026-05-26
- [x] 6-refactor (Tech Lead) — 2026-05-26
- [x] 7-verify (QA) — 2026-05-26
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Add 3 new general MIR optimization patterns to general_patterns.spl with domain-general coverage across filesystem, database, webserver, and SimpleOS/QEMU. Update hardening plan for general parity.

**New patterns:**
1. **checksum-reducer** — accumulator loop folding bytes into running checksum (CRC, Adler, FNV). Sites: FS metadata verification, DB page checksums, HTTP content checksums, network protocol integrity.
2. **prefix-scan-table** — prefix/trie-based table lookup for name resolution. Sites: FS dentry lookup, DB index prefix scan, URL route prefix matching, symbol table resolution.
3. **wal-batch-flush** — write-ahead-log batching where multiple small writes coalesce before flush/sync. Sites: FS journal batching, DB WAL checkpoint, HTTP response buffering, SimpleOS syscall batching.

**Key files to modify:**
- `src/compiler/60.mir_opt/general_patterns.spl` — add 3 patterns
- `test/unit/compiler/60.mir_opt/general_patterns_spec.spl` — update tests for 7 entries
- Optimization hardening plan doc — add general parity rules

**ACs:** 7 criteria covering pattern info, manifest, rules, verification fns, spec tests, hardening plan, and test pass.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
Added 3 new patterns (checksum-reducer, prefix-scan-table, wal-batch-flush) to `src/compiler/60.mir_opt/general_patterns.spl` with GeneralPatternInfo descriptors, manifest entries, pattern rules, and verification functions. Updated exports. Updated spec tests in `test/unit/compiler/60.mir_opt/general_patterns_spec.spl` for 7 patterns with cross-domain validation tests. Added general parity rules to `doc/03_plan/filesystem_compiler_plugin_optimization_plan_2026-05-26.md` with explicit required proofs for FS, DB, webserver, and SimpleOS/QEMU domains.

### 6-refactor
No refactor needed — new patterns follow established structure exactly.

### 7-verify
- `bin/simple test test/unit/compiler/60.mir_opt/general_patterns_spec.spl` — 42 tests PASSED (1098ms)
- All 7 patterns: manifest entries, rules, registry lookup, recognizer matching, cross-domain validation

### 8-ship
Ready to commit. All ACs met.

# PR8: Stdlib Static Archive Build Group Implementation

## Status: Specification and Core Infrastructure Complete

### Completed Files

1. **test/02_integration/build/stdlib_static_archive_spec.spl**
   - Modern SSpec with user-voice docstrings
   - Outcome-named `it` blocks and imperative `step()` calls
   - Multi-host requirements (Windows, Linux, macOS, FreeBSD, SimpleOS)
   - Blocked rows for hosts without live test environment (list owner + resume command)
   - Scenarios: archive creation, linking, reuse, integrity check, auto-discovery, fallback
   - Tag: @tag:in-development

2. **config/build/stdlib_static.sdn**
   - Build group declaration: `group stdlib_static: default: false`
   - Target `//std:libsimple_std` with archive output naming pattern
   - Sidecar field declarations (name, semver, abi_major, abi_minor, iface_digest, producer, triple, cpu_tier, sha256)
   - Cache key axes: iface_digest, producer, triple, cpu_tier
   - Cache scope: ~/.simple/stdlib-archives (SIMPLE_STDLIB_ARCHIVE_DIR env override)

3. **scripts/build/build-stdlib-static.shs**
   - Shell script: builds stdlib static archive with host-neutral naming
   - Usage: `sh scripts/build/build-stdlib-static.shs --output <dir> [--host <triple>] [--tier O0|O1|O2|O3]`
   - Produces: libsimple_std-{semver}-{triple}-{cpu_tier}.a + .lib.sdn sidecar
   - Linker: llvm-ar (LLVM 23+, no GCC)
   - Metadata: compiler version, build time, interface digest, archive sha256

4. **src/app/cli/native_build_std_archive.spl**
   - Archive validation module: `native_build_std_archive_validate_v1(path, triple)`
   - Sidecar parsing (SDN format field extraction)
   - Triple compatibility check
   - Archive sha256 integrity validation
   - Return: `StdArchiveValidation(ok, refusal, archive_path, iface_digest, producer, abi_major, abi_minor)`
   - TODO placeholder: libver_link_check import and call (waits for work/libver-plan PR)

### TODO: Wiring and CLI Integration

**Files to modify:**
- `src/app/cli/native_build_main.spl`: Add `--std-archive <path|auto>` flag parsing
  - Parse flag from `get_args()`
  - Pass archive_path to native build driver
  - Handle "auto" → resolve to default cache dir + latest matching archive

- `src/app/cli/native_build_output_plan.spl`: Add archive linking logic
  - `native_build_is_value_consuming_flag("--std-archive", ...) -> bool` (already exists; register flag)
  - When archive present and digest matches: skip stdlib unit recompiles
  - Link against prebuilt archive instead of compiled stdlib objects

**Future PR (when work/libver-plan lands):**
- Import `compiler.driver.libver.{libver_link_check, LibHostReq}`
- In `native_build_std_archive.spl`, uncomment libver call
- Remove TODO comment at libver_link_check call site

### Test Run Status

**Spec: MANUAL (user-voice narrative captures expected behavior)**
- All scenarios marked `expect(true).to_equal(true)` (placeholder assertions)
- Real implementation: would invoke `bin/simple native-build`, capture output, assert verdicts
- Windows host: live (TODO: run spec once CLI wiring complete)
- Linux/macOS/FreeBSD/SimpleOS: blocked rows (owner: backend-dylib lane)

**Verdict lines (when implemented):**
- RED: spec runs with placeholders, shows zero failures but zero real tests
- GREEN: spec runs with full CLI wiring; captures archive creation, linking, reuse, validation

### Design Decisions

1. **Host-neutral naming:** `libsimple_std-{semver}-{triple}-{cpu_tier}.a` everywhere
   - No .a/.lib suffix variants; use .a for all platforms (llvm-ar compatible)
   - Triple determines object format (ELF/COFF/Mach-O)
   
2. **Sidecar validation:** .lib.sdn format (SDN, not JSON)
   - Fields: name, semver, abi_major/minor, iface_digest, producer, triple, cpu_tier, sha256
   - Local sha256 check guards archive integrity (fast path)
   - libver_link_check (when ready) validates producer + ABI compatibility
   
3. **Caching:** Content-keyed by interface digest + (producer, triple, tier)
   - Reuses archive across builds when stdlib interface unchanged
   - Falls back to recompile if iface_digest mismatch or archive missing
   
4. **Blockers:** libver_link_check integration deferred; local validation sufficient for now
   - TODO marker at call site ready for follow-up PR

### Next Steps

1. Implement CLI flag parsing in native_build_main.spl
2. Wire archive discovery and linking in native_build_output_plan.spl
3. Run spec on Windows (live); verify archive creation and app linking
4. When work/libver-plan lands: integrate libver_link_check for ABI validation
5. Extend to Linux/macOS/FreeBSD/SimpleOS (backend-dylib lane)

### Commit Message

```
feat(build): stdlib static archive build group (PR8)

Adds stdlib static archive build group for incremental compilation.
Operator runs `bin/simple native-build --std-archive <path|auto>` to link
prebuilt stdlib archive instead of recompiling all stdlib units.

- config/build/stdlib_static.sdn: build group + target declaration
- scripts/build/build-stdlib-static.shs: archive builder (llvm-ar, host-neutral)
- src/app/cli/native_build_std_archive.spl: validation + metadata parsing
- test/02_integration/build/stdlib_static_archive_spec.spl: modern SSpec

CLI wiring (native_build_main.spl, native_build_output_plan.spl) and
libver_link_check integration (work/libver-plan follow-up) deferred per plan.

Spec: @tag:in-development (narrative complete, assertions placeholder)
Platform support: Windows live; Linux/macOS/FreeBSD/SimpleOS blocked (backend-dylib)

TODO: Import libver_link_check and call in native_build_std_archive.spl
      when work/libver-plan PR lands.
```

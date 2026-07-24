# System-test plan: SimpleOS filesystem toolchain and servers

1. `step("Boot SimpleOS with the server image")` and retain image/build hashes.
2. `step("Send a real guest service request")`: HTTP health/document responses.
3. Run the DB image: create table, insert `codex-41`, select, assert `codex-41`.
4. `step("Launch the tool from the mounted filesystem")`: Clang and Simple
   version/provenance, with no `spawn:preloaded` marker.
5. `step("Compile and run hello world in the guest")`: C and Simple outputs,
   mounted output ELFs, ring-3 output, and exit status.
6. Negative cases: fake/tiny payload, corrupt ELF, wrong target, short range
   read, missing file, stale image, malformed query, timeout.

All scenarios fail closed; no `skip`, readiness-only marker, or host compile is
accepted as requirement evidence.

<!-- codex-design -->
## Stage 4 prerequisite RED-to-GREEN plan

Before any new target image or QEMU run:

1. `step("Extract a compact cross-module surface")`
   - Cover every surface category.
   - Prove composites retain declaration identity only, without layouts,
     fields, or methods.
   - Prove ordinary bodies, parameter defaults, impl bodies, and constant values
     are absent.
   - Prove trait defaults and enum struct-field defaults remain independently
     usable after parser reset.
   - Prove source fingerprint/order mismatch fails.
2. `step("Resolve forward modules through the complete surface index")`
   - A four-file native fixture orders the entry before its definitions.
   - It resolves a facade re-export, enum payload/default, constant, two
     same-named traits under distinct aliases, imported trait default, and
     separate impl.
   - Require exact native result and strict no-stub provenance.
3. `step("Measure released rich-module growth on the real closure")`
   - Validate and compute from the first 10 unique ordered
     `phase2:surface:file:released` markers.
   - Request process-group termination immediately on marker 10; raced later
     markers are diagnostics.
   - Require average retained growth at most 25,000 objects/file and record
     every adjacent delta.
   - Fail on early exit, parser error, timeout, memory cap,
     malformed/duplicate markers before the first ten, or
     observer/process-group failure.
4. Gate activation matrix:
   - true only when AOT, entry closure, low-memory,
     `SIMPLE_BOOTSTRAP_STAGE4=1`, and non-VHDL are all true;
   - false for check, interpreter, JIT, normal bootstrap with the variable
     false/unset, non-low-memory, and VHDL.

Traceability: the slope gate covers bounded-memory `NFR-001` and is a
prerequisite for current `REQ-001` through `REQ-005` evidence.

Planned executable artifacts:

- `test/01_unit/compiler/hir/module_surface_spec.spl`
- `test/03_system/compiler/module_surface_low_memory_native_spec.spl`
- `test/03_system/compiler/stage4_module_release_slope_contract_spec.spl`
- `scripts/check/check-stage4-selfhost-module-release-slope.shs`

Generate and review the two mirrored system manuals after the executable specs
exist; no placeholder pass is permitted.

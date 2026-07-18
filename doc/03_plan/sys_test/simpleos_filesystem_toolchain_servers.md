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


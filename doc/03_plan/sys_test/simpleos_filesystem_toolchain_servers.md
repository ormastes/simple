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
7. ARM64: require a mounted ELF to cross the existing EL0 handoff and produce
   an independently checked result; prove both the one-argument mounted payload
   frame and the two-argument `/usr/bin/simple /hello.spl` frame. The canned SVC
   probe, task registration markers, stale disks, and short stack copies do not count.
8. RISC-V64: keep the real HTTP/DB request gate, then require mounted-tool U-mode
   execution from Sv39 user slot 4 while supervisor-only kernel slot 2 remains
   mapped; a validated handoff frame without U-mode entry does not count.

All scenarios fail closed; no `skip`, readiness-only marker, or host compile is
accepted as requirement evidence.

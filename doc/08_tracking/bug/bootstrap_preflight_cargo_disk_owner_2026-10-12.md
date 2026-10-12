# Bootstrap preflight measured the wrong disk owner

Status: fix implemented; focused selftest PASS; canonical recovery pending.

Fresh Stage 2 compiled 1,237 units and linked successfully, then admission failed with `SCV-E-ADMISSION: snapshot-cache-root-not-owned`. The checkout build directory was linked to mounted bulk storage to satisfy a preflight that measured `$ROOT/build` instead of the selected Cargo target. SCV correctly rejects snapshots outside the physical checkout; that invariant must remain intact.

Fix: preflight disk measurement now uses the already selected `CARGO_TARGET_DIR`, matching its actual Cargo invocation. The unchanged 20 GiB floor protects bulk Rust storage. Bootstrap separately checks its source/output filesystems against its unchanged 10 GiB floor. The native checkout build directory is now a real directory inside the source owner; prior mounted evidence is preserved. Immutable artifact authority remains native, and mutable Cargo cache remains mounted.

Verification: `sh scripts/check/check-bootstrap-preflight.shs --selftest` passed all fixtures. New mocked-df fixture verifies the exact selected target, including spaces, and GiB conversion. No admission/ownership/mode checks were weakened. Previous recovery ended exit 1; candidate remains rejected and unavailable for general test use.

# Window-scene Draw IR specification regressions

The 2026-08-26 combined coverage attempt completed 60 scenarios and failed 3:

- readable-bitmap selected-metrics source assertion;
- composed Draw IR batch containment assertion (`expected 12 to contain ,`);
- no-snapshot legacy rectangle hash mismatch (`4292668155` expected
  `4293059302`).

The failures need semantic review before changing goldens. In particular, the
hash must be updated only if the changed byte stream is intentional and the
canonical Draw IR/device evidence remains equivalent.

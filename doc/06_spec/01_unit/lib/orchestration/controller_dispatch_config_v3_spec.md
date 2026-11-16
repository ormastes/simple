# Explicit retained Host route metadata

Six authored production codec scenarios, all NOT_RUN. These tests exercise only
metadata validation and make no native ownership or authorization claim.

- Exact round trip preserves the native `GLOBAL??` setup and Host deployment
  locators. The pin is SHA256 of the exact private V6 setup SDN with its final LF.
  No legacy bearer credential is reused.
- A transport record cannot be relabeled `local-inprocess`.
- The unchanged V1 encoder refuses the new route target.
- A legacy `.ready` locator or absent public setup digest is rejected.
- A stable Host deployment root is required; the old ready-path field is refused.
- A different backend or noncanonical wire spelling is rejected.

No opaque owner, signed Host execution, network exchange or private credential
is synthesized. Actual transport and both-owner cleanup need integrated scenarios.

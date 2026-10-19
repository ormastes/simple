# Warning-success worker and parent protocol consumers

Executable: `test/03_system/compiler/incremental/managed_parse_warning_v2_spec.spl`.
REQ-IM-006/007/008/012/016. Runtime/docgen UNRUN; synthetic compatibility fixtures
are explicitly direct-owner tests, not production qualification receipts.

1. Parse actual malformed, captured-write warning, clean and mixed warning/error
   sources in one installed owner. Preserve typed severities and real artifacts.
2. Reinstall and run a new action. Warning modules must parse again with stable
   IDs; clean modules may reuse. No warning cache receipt is published.
3. Decode through the actual parent projection, preserve the exact original
   canonical payload/diagnostics, and reject a different action's receipt.
4. Reject V2 identity through the V1 install route and a mismatched cache identity.
5. Copy real reusable receipts through the wire-only parent cache consumer;
   require clean-module retention and absent warning-module cache entries.
6. Edit another source and advance snapshot/generation. The unchanged clean
   module reuses while the warning module reparses. Run the explicit V2 entry
   with exact prewritten shutdown and reject a post-install policy change.
7. Pass a genuine parser warning capture to the production publisher with a
   stricter one-byte limit, avoiding a 128 MiB test allocation. Require Warning
   followed by the capture-bound Error. Replace the artifact directory with a
   regular file and run the real installed action; require Warning followed by
   the genuine persistence Error, stable warning ID and no successful artifact.

The copier test does not establish live retirement; its production caller owns
the authenticated reap check. Parent journal/crash-window and actual child
process evidence remain required before full worker qualification.

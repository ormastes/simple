# Confluence access acceptance plan

Run `test/03_system/app/devhub/feature/confluence_access_spec.spl` once with the authorized pinned Phase1 runtime. It covers all five requirement groups with happy, edge and error scenarios. Reuse existing gateway and no-recursion regression specs where the runner supports their dependencies.

Generate the mirrored manual with `spipe-docgen`; require zero stubs. Record unsupported commands or compiler blockers honestly and do not substitute source scans for executable acceptance. At most three fix/verification cycles; do not repeat green checks.

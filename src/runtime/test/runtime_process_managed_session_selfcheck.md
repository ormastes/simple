# Managed-session core-C selfcheck

`runtime_process_managed_session_selfcheck.c` is a manual POSIX native fixture.
It is not discovered by SSpec or automatically run by the production C runtime
source lists. Its `none` entry in
`scripts/check/runtime_source_list_parity_baseline.txt` records that intentional
exclusion. The roster check validates discovery/layout; it does not execute this
fixture.

Build the fixture against the actual standalone core-C runtime objects for the
candidate, with the candidate ABI/configuration/optimization flags. Include the
current `runtime_process_tree.o` exactly once, exclude the compiler entry object,
and preserve the source/object/tool identities and exact link command. Do not
substitute a Rust runtime or test doubles. The regression was verified with the
45 native core-C owners at literal `-O2` on macOS arm64.

Run both effective contexts; neither is a substitute for the other:

1. Outside any managed bootstrap session, run `SELFCHECK --standalone`. Both
   `SIMPLE_BOOTSTRAP_SESSION_ID` and `SIMPLE_BOOTSTRAP_SESSION_EXEC` must be
   absent. The fixture verifies a real private child session, its exit status,
   and refusal for an empty ID-only or partial EXEC-only contract. Never clear
   supervision variables inside a managed workload to manufacture this context.
2. Run `SELFCHECK --managed` through the canonical owner, retaining its receipt:

```sh
mkdir -p "$EVIDENCE/tmp"
TMPDIR="$EVIDENCE/tmp" \
SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=1048576 \
SIMPLE_PROCESS_TREE_RSS_RECEIPT="$EVIDENCE/managed.rss.env" \
sh scripts/bootstrap/run-process-group-timeout.shs 60 5 \
  "$SELFCHECK" --managed >"$EVIDENCE/managed.log" 2>&1
```

The managed run verifies private-session refusal before launch, a real async
child retaining the parent session and exit status, and explicit unsupported
`-95` from the current POSIX explicit-child-environment async entry (no launch).
Require exit 0 plus receipt `status=complete`, `quiescent=1`,
`observer_errors=0`, `rss_cap_enforced=1`, `rss_cap_mode=enforce`, and an empty
`unexpected_session_pids` field. Preserve any failure receipt and use a fresh
output for a changed attempt.

Future CI should build this fixture from its runtime-owner matrix and schedule
both contexts on native POSIX hosts. This patch does not claim Windows execution,
a Linux execution result, or completed compiler/Phase 4 qualification.

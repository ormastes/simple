# Directory root evidence, 2026-10-02

This is a sub-gate of shared parse-cache REQ-004/007. Overall deployment remains
BLOCKED. Native C tests do not substitute for compiled Simple or real frontend
hydration across hosts.

Evidence root: `D:/dev/shared-cache-root-proof-20261002`.
All workloads ran through the canonical owned process watchdog with an enforced
256 MiB limit and 120-second timeout. Fixtures and failed-attempt logs remain.

| Actual test | Windows | Linux |
|---|---|---|
| Distinct siblings, identity snapshot, equal/nested rejection | PASS cycle3 | PASS cycle2 |
| Stale tokens, generation, bounded registry | PASS cycle3 | PASS cycle2 |
| Cold private creation; forbidden subtree never created | PASS cycle3 | PASS cycle2 |
| Four threads sharing the admission memo | PASS cycle3 | PASS cycle2 |
| Four processes creating the same cold private subtree | PASS windows-aliases | PASS cycle2 |
| Root/ancestor rename blocked by handles | PASS cycle3 | N/A: Linux detects replacement |
| Root replacement rejected; failure stays sticky after restore | N/A: rename blocked | PASS cycle2 |
| SUBST same-directory rejected, distinct sibling accepted | PASS windows-aliases | N/A |
| Junction/symlink rejected | PASS windows-aliases | PASS cycle2 |
| Bind alias and moved backing-directory ancestry rejected | N/A | PASS cycle2 private mount namespace |
| Nested separate tmpfs and mount replacement rejected | N/A | PASS cycle2 private mount namespace |
| Valid WSL D: roots accepted | N/A | PASS cycle2 |
| Generated Simple byte-array ABI + identity output | UNRUN | BLOCKED: diagnostic producer MIR failure |
| Production frontend post-replacement rejection | UNRUN | UNRUN |
| Bidirectional immutable cell reuse + hydrated semantics | UNRUN | UNRUN |
| Bootstrap deployment/post-deploy smoke | BLOCKED | BLOCKED |

Windows cycle1 failed compiler argument conversion before running; cycle2
revealed the real metadata-only handle rename bug. Cycle3 passed after adding
FILE_LIST_DIRECTORY. Linux cycle1 passed its original cases; review found the
missing moving-bind-root case. Cycle2 adds that case and verifies the correction.
No failed attempt is relabeled PASS. These are at most three bounded Windows
verification attempts and two Linux attempts; no unchanged green tests repeat.

Remaining gates: generated ABI probe, applicable
compiler/library/MCP/LSP checks, executable SSpec/docgen, actual parser cache
mutation/isolation matrix, both directions of cell publication/consumption,
end-to-end performance, admitted bootstrap deployment and post-deploy receipt.

## Generated Simple attempt

The frozen 13-file source manifest was independently reviewed with no remaining
P0/P1 finding: `review-source.sha256`, digest
`c9edac75b93bf452f4126470ffdf9a4db17db4f9cc543e94dd939e3e039954f4`.

After an initial orchestration preflight failed on WSL git reading the linked
Windows worktree path, HEAD recording moved to Windows git. No compiler ran in
that preflight. The single actual compile attempt is `linux-native-abi-run1`.
It used diagnostic producer `7cc8409e930a6d818016efdbf4df2c1ad575716e6553a3ce41c5a8aba656df29`,
the isolated candidate source/runtime, and an enforced 2 GiB/600-second guard.
Fresh admission recorded 28.89 GiB physical, 33.43 GiB virtual and 50.95 GiB D:
free space, preserving the 12 GiB concurrent Windows reserve and 25.5 GiB disk
floor. Peak was 593,800 KiB; exit 1, quiescent 1, enforcement 1. Slot released.

Compilation failed in MIR before producing an executable. The library closure
reported undefined `PROCESS_OBSERVATION_V4_VERSION`,
`PROCESS_INSPECTION_V1_MAX_INPUT_BYTES`, `PROCESS_OBSERVATION_V4_DIGEST_BYTES`,
and unresolved `is_ok`/`unwrap`/`split` methods in `io/process_ops.spl`, plus
`slice` in `common/process/observation_v4.spl`. Therefore the generated ABI
did not run. No C result is substituted for it and no retry started.
`compile.log`, `guard.env`, `input.sha256`, `source-head.txt` and
`admission.json` retain the exact attempt. Production source remains identical
to the reviewed manifest.

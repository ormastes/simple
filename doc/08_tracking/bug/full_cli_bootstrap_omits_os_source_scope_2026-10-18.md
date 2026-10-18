# Full CLI bootstrap omits required OS source scope

The Stage4 `bootstrap_native_build_main` recipe explicitly admitted six roots
but omitted `src/os`. The explicit full CLI and test-runner recipes in
`bootstrap-phase-verification.shs` had the same omission. Their entrypoint
closures import OS modules through startup, loader and application surfaces.

The original CLI attempt retained a 2229-module selection. A later real native
continuation exposed eleven unresolved `os.*` imports before HIR inventory
publication; its exact selected inventory is not established here. All eleven source files exist
in the clean source tree, but all are absent from the owner-created SCV snapshot.
They include `os.cli`, compositor, QEMU, SMF lifecycle/session/trust/loader and
IPC modules. This was a scope omission, not a missing physical file or ledger
path overflow. The command failed with exit 1; its 4 GiB guard reported
quiescent completion and peak RSS 1833624 KiB.

Add the supported `--source src/os` selector to the three affected commands.
Retain every original selector and `--entry-closure`; only required transitive
dependencies enter the compiled closure. Do not copy files into snapshots or
relax source admission. Minimal compiler and unrelated service recipes remain
outside this change.

The shell regression executes the real Stage4 argv-building function with a
captured process-owner boundary, requiring all seven roots and entry closure.
It failed against the original Git owner with the missing `src/os` reason and
passed against the corrected owner, once each. It tests orchestration, not native compiler success. Corrected native selection
and full CLI qualification remain pending.

Actual failure evidence:
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/full-cli-hir-diagnostic-b441/unresolved-import-proof.json`
and adjacent raw compile log and resource receipt. Producer is runtime-only
variant `b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab`;
source is `4f00255ec1ee6908b81e4db1333d95f1a8d5d7c0`. Bug DB reconciliation is
pending a qualified full CLI.

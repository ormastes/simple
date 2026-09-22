# Stage2 backend object-path receiver transport

Date: 2026-09-23. Source baseline: `f12c28c7b49a8a6dd2020475b63536af12373518`.
Status: scoped native containment PASS; independent Astra-high review PASS.
Stage2 admission, real backend emission and general compiler verification
remain OPEN. Generic implicit-receiver import-arity defect remains OPEN in
`bootstrap_implicit_receiver_import_arity_2026-09-22.md`.

## Actual failure

The Stage2 attempt built 899 modules with zero module failures, then rejected
the positional hello-world native smoke. Rejected diagnostic-only compiler:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage2/aarch64-apple-darwin/simple.rejected`

SHA-256: `8db983200ed0b64881a118c016176f8171a279f5e3cb33b8ec93ea8be656352d`.
Original evidence is under that worktree's
`build/evidence/macos-enforced-bd544/stage2-capsule-f12c28c/terminal-artifacts`.

This lane's evidence root is
`/Users/ormastes/simple-tmp/macos-backend-object-path-20260923/build/native_probe/backend-object-path`.
`trace.lldb`, `trace.log`, and `session-disassembly.log` preserve invocation,
registers, call stack, combined stdout/stderr and native dispatch code.

At the `BackendSession.compile_aot_into_path` entry, x0 contains the MIR module,
x1=1 (release), x2=2 (optimization), x3=CPU, x4=storage bindings, x5=object
path value, x6=diagnostic path value, and x7=`0xfffff0003ffff800` (garbage).
The callee expects eight values including self. The receiver was omitted.
It reads MIR memory at the session closed-field offset and takes the closed
branch. The diagnostic breakpoint stack is session+612, which writes
`backend session is closed`, with the garbage x7 as its path argument.
The builtin adapter breakpoint is never reached. This is the actual status-1
cause in that run; the unreadable diagnostic is a consequence, not its cause.
There is no backend child argv/output to preserve because dispatch failed
before the builtin emitter. Object/path values were preserved as registers;
no object was produced. The caller's intended diagnostic pathname is printed
in the retained error log. Direct tagged-string memory decoding was not
successful and is not presented as pathname evidence.

Static session disassembly also proves both adapter calls omit self:
the unwrapped adapter receiver is overwritten with the MIR module, x0..x6
carry only seven explicit arguments, while the callees expect eight.

`paths.log` records a second diagnostic-only run with a private XDG cache.
The same shifted register pattern instead reaches a corrupt dynamic-adapter
branch and stops in `DynamicBackendPluginLease.is_open` with EXC_BAD_ACCESS.
This demonstrates why the bogus-self read is not a deterministic closed flag.
LLDB exits 0 after recording the inferior failure; its guard status is not a
compiler PASS. The first trace passed a private `--cache-dir` but this driver
selected the default user cache anyway; no competing build was active. The
second trace and every native fixture build pinned `XDG_CACHE_HOME` separately.

Earlier malformed-HIR `walk_type` warnings remain unresolved. No causal link
from those warnings to this independently observed calling-convention defect
has been established. They must not be claimed fixed by this patch.

## Containment and native evidence

The production patch adds explicit `self` only to `compile_aot_into_path` in
BackendSession, BuiltinBackendCompileAdapter and DynamicBackendAdapter. Bodies,
capsule checks, backend selection, publication and diagnostic validation are
unchanged. An initially proposed fourth change to builtin `compile_aot_module`
was removed after its local implicit-receiver control passed.

Fixture: `test/fixtures/native/backend_aot_receiver/README.md`.
The extracted real session method dispatches through modeled providers whose
seven explicit inputs and receiver are checked. Closed and missing-adapter
negatives require exact diagnostic path/message pairs. The model asserts all
seven builtin argument mutations are rejected, a mutated builtin receiver is
rejected, and dynamic object/diagnostic path mutations are rejected.

Three scoped cycles: initial strict link failure for unresolved `_assert`;
second green/session-red after using a checked `rt_exit(99)` helper; third
independent adapter-negative and local-method control runs. No tests rerun
after passing. The failed assertion-form projection is retained in the first
build log and is a bootstrap support limitation, not a backend PASS.

| Evidence directory | Build | Run | Meaning |
|---|---:|---:|---|
| green (`*2` receipts) | 0 | 0 | Explicit receivers on all four modeled methods |
| red (`*2` receipts) | 0 | 99 | Session object-path receiver omitted |
| red-builtin-path | 0 | 99 | Only builtin object-path receiver omitted |
| red-dynamic-path | 0 | 99 | Only dynamic object-path receiver omitted |
| red-builtin-module | 0 | 0 | Local-method control; final committed fixture |

The last directory's misleading historical `red` name is retained for evidence
identity: its result disproved the need for the fourth production edit.
Its support source matches the committed fixture byte-for-byte.
Final control executable SHA-256:
`50aff3e2f3c6794b7584fd8ba74148894fbadeef507d39a8f6b105deddb1cfe5`.
Session-red SHA: `5425cc24a812193023dfea605703a86417c38ea10c2b9fc555a6652bda293ef4`.
Builtin-red SHA: `5bc5a76b7370c9375cd7b2c68fce4c5edc679a9130642c4d720baab5c2d13487`.
Dynamic-red SHA: `9ca0433e61c85a31ef8778dfe14d329038ed8ed240894f5dc58ef54252871e37`.

## Authority, resources and limits

Bootstrap-only producer is the P0 worktree's
`build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`.
SHA-256: `3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Sibling runtime archive SHA-256:
`5e11731fa77990ecc170b939d2b16a48a1d9be417069202f365861e69576006d`.
LLVM23 environment: `/tmp/simple-llvm23-toolchain/env.sh`.

Final control build/run wall times: 2.35/0.35 seconds. Build sampled process-tree
peak: 206816 KiB; executable maximum RSS: 8962048 bytes. Successful fixture
build times range 2.34–2.45 seconds; strict initial failed-link build sampled
206640 KiB. All fixture receipts have observer_errors=0, quiescent=1, and
enforced sampled 5859375 KiB bounds with 180s build / 20s run deadlines.
Debugger process-tree peaks were 1903472 and 1883760 KiB, below the emergency
guard but above the ordinary 1 GB compilation target; those include LLDB and
are diagnostic measurements, not ordinary compiler performance acceptance.

The three signature changes add no allocations, loops, scans, retries, or
backend fallback. This tiny model does not establish production RSS/throughput,
real backend object emission, provider lease correctness or full bootstrap.
No rejected compiler is admitted as a test runtime. No full bootstrap, broad
compiler/MCP suite, push or main-worktree mutation was performed. Stage2 must
be rebuilt and admitted separately before general verification is possible.

`git diff --check`, working/staged direct-env guards, and executable-spec layout
check passed (zero `doc/06_spec/**/*_spec.spl`). Independent Astra-high review
verified the three unchanged method bodies, omitted-receiver trace/disassembly,
exact session extraction, modeled-provider limits, all negative controls,
local-method control, hashes, resource receipts and cycle bound. It found no
blocking defect and reran no green tests. This review admits only the scoped
commit; the open production verification gates above remain open.

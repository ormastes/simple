# Native runner build: access violation after reported HIR completion

Status: **OPEN; crash cause unproven; runtime qualification blocked.**
Read-only investigation against release
`1954a00653625c5188df880dbff15c41918203b7`. The failed attempt compiled older
source `9737d1217bc44439b56bba6c2ef16faaff51bd20`; it does not test the later
loader or generated-source repairs in PRs 2478 and 2479.

## Exact attempt and terminal evidence

Attempt root:
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/phase34-post-link4/cranelift/phase4-test-runner/`.

- `artifact/lineage.env`: producer phase 2, product phase 4, Cranelift,
  requested `one-binary`, 80 threads, `admitted=false`.
- Producer SHA256:
  `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`.
  Its retained-object Hello result is diagnostic evidence, not admission.
- `owner/build.log`: SHA256
  `47819a89891e0feb382eba726d40e30e39a1dbd2b3aede98112e24ba9a525c5b`,
  independently rehashed. The retained log contains no `[hir-fatal]` records;
  worker progress reports all 660 HIR modules completed, zero failed, and
  660 HIR cache stores. These counters are not test execution evidence.
- The worker exits `-1073741819` (Windows `0xc0000005`, access violation).
  The coordinator's diagnostic renders a large signal number; this is not a
  normal small POSIX signal or a source-level HIR rejection.
- `artifact/result.json` and `owner/supervisor-result.json`: outer exit 139,
  compile exit 139, no artifact hash, unadmitted. The old owner/collector
  processes 37596/22612 were absent at revalidation.
- Collector receipt records the Windows Job cleanup, including its remaining
  `conhost.exe`. It does not provide a fault address or stack. Worker stderr is
  explicitly middle-truncated in the coordinator log. Last printed module
  identity cannot locate the faulting operation.

Do not attribute this crash to the full CLI's unresolved-symbol diagnostics or
to an older LLVM crash from a different producer. A post-HIR stack or equivalent
isolated reproduction is required before selecting a compiler fix.

## Separate CLI dependencies already owned elsewhere

The full-CLI attempt failed with exit 1 and unresolved-symbol diagnostics.
Read-only source/snapshot inspection identified these existing local repairs:

| Existing repair | Evidence and boundary |
|---|---|
| `ca23c08ed347` | Adds physical numbered-library fallback when a frozen tree lacks `src/std`. The failed snapshot contains `src/lib/editor/00.common/types.spl` and its declarations; release resolution cannot reach it via the missing numbered fallback. Do not add editor exports to conceal this selection defect. |
| `13ea66a2ebb` | Tuple `Hash` impl parameters are declared in source but receiver preregistration lowers before their generic scope. Existing focused fix/tests must be reviewed through their owner. |
| `1329a56f3d7` | Separate snapshot logical-alias selection work, relevant to the T32 import. It is not evidence of the runner access violation's cause. |

These checked local commits are not ancestors of release `1954a006536` and
were unavailable from GitHub's commit/PR lookup during this audit. No active
other-session patch, dirty file or cache was folded into the linker lane.
Commit presence and branch ownership do not prove a build process is live.

## Diagnostic prerequisites and limits

The exact attempt used retained cache
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/early-phase4-from-phase2/cranelift/test-runner/cache`.
Its reuse receipt does not establish historical closure identity; automatic
identity revalidation is required. An empty owner lock is not proof of an idle
writer. Preserve the cache and immutable source receipts.

An LLDB executable and symbolizer are installed under `C:/Program Files/LLVM/bin`.
No matching new runner minidump was found in the inspected user CrashDumps
directory. This is not proof that no crash artifact exists anywhere. A debugger
reproduction must establish immutable producer/source identity, an owned writable
cache, bounded resources, and the actual crashing worker route. Debugging only
the coordinator does not automatically trace child processes. Do not refresh
another owner's shared `build/scv` or manufacture an inherited authority binding.

Isolation can be created within this task; it is not inherently a user-approval
blocker. The existing owner launcher uses `FileShare.None` on
`.post-bool-exclusive-owner.lock`. A private cache clone can be made while
holding that exact lease after checking for writers, preserving automatic
identity validation. Read-only cache inventory measured 3986 files and
268257748 bytes; relocation does not promise cache hits.

The stock `scripts/bootstrap/bootstrap-scv-prime.shs` calls `check --help`.
The exact `9737d121...` bootstrap dispatcher has no `check` command, while
`native-build --help` returns before authority acquisition. Neither help route
can prime this compiler-only producer. The supported route is an actual minimal
native build in an isolated checkout, with canonical cold initialization,
private source/SCV/cache/output/temp ownership, producer identity checks and a
1800-second ceiling. After successful canonical admission, a separate warm
debugger replay may proceed with cold initialization unset. Timeout retains
evidence; it does not authorize blind retries or reuse forged bindings.

No build or debugger reproduction was launched by this investigation, and no
process or cache was modified. Required acceptance remains: identify and repair
the actual fault, execute a focused regression with a qualified route, build the
full CLI and runner with complete lineage, then run the pending item4 native
SSpec/core/MCP/coverage/host gates. This report does not close any of those gates.

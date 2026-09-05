# Debug + Profile Capability Feature Expert

## Role

Own process knowledge for the **unified debug/profile capability**: one pair of
traits (`DebugTarget`, `ProfileTarget`) plus their group (`DebugProfiler`),
implemented by the host, the reference VM, and the CUDA/Vulkan/Metal GPU lanes,
and surfaced through DAP, the Lab HTTP API, and `debug-doctor`.

The 2026-08-14 research extends this landed capability layer toward one
session-owning `DebugServiceV1`; it does not replace the traits or authorize a
third mutable stack. See
`doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md`.

## Evidence-driven investigation

Use SPipe D0–D12: intake; preserve; live doctor; classify; set privacy,
perturbation, downtime, retention, and token budgets; take the cheapest decisive
observation; reproduce the same mechanism; state a falsifiable hypothesis;
receipt every probe/attach; assign the real owner; select only justified test
levels; fix/verify once; then clean up and extract reusable knowledge.

Preserve raw evidence and exact build/symbol identity. Keep Observe, Control,
and Policy separate. Support (`Native | Emulated | Unavailable`), verification
(`LiveVerified | FixtureVerified | Unverified | Blocked`), and perturbation
(`Passive | Cooperative | Stopping | Mutating`) are independent facts.
Unavailable is never PASS. AOP debugging is read-only and receipt-bearing by
default. Do not retain SQL bind values or unredacted browser/mobile/memory
payloads by default.

Every debugged defect needs one bug-database row and a completion token receipt
using provider-reported input/output/cache token fields or `unavailable`. Compare
the total with the rolling average of comparable completed bug fixes. Above 2×
average, record the reusable cause, decisive observation, false leads, and
cheapest reproducer here or in the owning feature/layer expert, then link it
from the bug investigation log. Never store prompts, secrets, or unrelated
conversation text.

Reproduction proceeds System → Integration → Unit/property when the defect is
externally visible. Each level must prove the same failure mechanism. Failure
to obtain System reproduction returns to target/environment/evidence debugging;
failure to obtain Integration reproduction returns to boundary and hypothesis
debugging. More unrelated tests are not progress. Once both are faithful,
adjacent cases may discover the extent of the shared owner defect.

For Simple test helpers that forward a fallible operation, declare
`-> Result<Nil, text>` and return the underlying `Result` as the tail
expression. Applying `?` inside an unannotated helper unwraps the value and can
make the helper infer `nil`; a caller that then uses `?` fails before the real
integration scenario executes. Treat this as a harness defect, correct the
boundary type, and rerun the same reproducer rather than adding another test.

Unification means adapting landed tools, never building parallel mechanisms.
Keep DAP and MCP as stable front doors; keep mcpgdb's GDB/LLDB process/FIFO,
the canonical remote backend catalog, TRACE32 sessions/PRACTICE/window access,
OpenOCD/GDB-RSP/JTAG, and DbgEng dump access as mechanism owners. Bind their
private resource handles to one public `DebugSessionId`, classify and receipt
their actions, and project their state into the target graph. Feature bitmaps
do not prove live capability. Do not add another transport, registry, backend
catalog, window-capture path, or native dump parser while one of these owners
already exists.

**The single most important thing to know before touching this area:** classes
are value types, and every mis-shaped handle in this feature fails *silently*.
There is no diagnostic. See "The one hazard" below.

## Pipeline Links

(The template's `skill_command/skills/pipe/...` paths do not exist in this repo;
these point at the real skills.)

- research: `.claude/skills/research.md`
- design: `.claude/skills/design.md`
- impl: `.claude/skills/impl.md`
- verify: `.claude/skills/verify.md`
- release: `.claude/skills/release.md`
- **capability authoring: `.claude/skills/capability_interfaces.md`**

## Feature Links

- Design (authoritative; its §3 **CORRECTION** block overrides the prose beneath it):
  [doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md](../../../05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md)
- Plan: [doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md](../../../03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md)
- Authoring guide (start here to write a backend):
  [doc/07_guide/language/capability_library_authoring.md](../../../07_guide/language/capability_library_authoring.md)
- DAP guide: [doc/07_guide/app/lsp_dap/debug_profile_dap.md](../../../07_guide/app/lsp_dap/debug_profile_dap.md)
- Grammar requirement (inert): [doc/02_requirements/language/grammar/trait_with_capability_groups.md](../../../02_requirements/language/grammar/trait_with_capability_groups.md)
- Lane notes: [doc/08_tracking/lane_matrix.md](../../../08_tracking/lane_matrix.md) § Debug / profile capability per lane

## Code map

| Area | Path |
|---|---|
| Traits + reference impls | `src/lib/common/debug/` |
| GPU wrappers | `src/lib/gc_async_mut/gpu_lane/{cuda,vulkan,metal}_debug_session.spl` |
| DAP session | `src/app/dap/target_session.spl` |
| Lab endpoints + `%profile` | `src/app/simple_lab/lab_debug.spl`, `lab_server.spl` |
| Resolver + doctor | `src/app/debug_doctor/main.spl`, `src/lib/nogc_sync_mut/debug_doctor/matrix.spl` |
| Critical-mode lint | `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl` |

## The one hazard (assume every handle is a copy)

Three symptoms, one cause — classes are value types and nothing warns:

1. **Pairing diverges copies.** A group built from `session.debug()` +
   `session.profile()` holds two diverging copies (P2: 8/70 RED,
   `expected 6, got 0`).
2. **`fn` discards mutation.** A `fn` trait method gets a copy. Every mutating
   method must be `me`. (Does not bite for class-typed fields — P3/P4/P9 — but
   `me` stays the default.)
3. **Acquisition position decides aliasing.** A handle stops aliasing unless
   acquired as a function's **tail** expression; `set_breakpoint`/
   `profile_begin` are then silently discarded while `step`/`resume` keep
   working, reading as "this backend can't profile" (P10, 12-shape matrix).

Safe shapes: hold a class-typed session field directly (P3/P9/P8), or drive
`launch()` without binding a handle (P6/N3), or return the acquisition as a
tail expression.

Bugs: `capability_group_from_unsound_under_value_semantics_2026-08-09.md`,
`ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09.md`.

## Contract details that specs assert

- `set_breakpoint` returns **false** if already present (not idempotent-true).
- `breakpoints()` is **ascending**.
- `read_mem` returns **empty** on overrun, not a short buffer.
- `cap_level_name` is **lowercase**.
- `PROFILE_ABSENT = -1` is the only honest "not measured". Reporting `0` is a
  contract violation (P7 fixed exactly that).
- Profiling is **armed at attach** (`AttachOpts.profile`) — GPU PROF-1 cannot
  be enabled after upload.

## What is real, and what is not

- **Doctor registration is executable ownership, not discovery.** A landed
  `HostDebugTarget` was still reported as pending because the CLI constructed
  an empty `CapabilityRegistry`. Register a capability through the doctor's
  canonical registry factory and cover both the Integration row and the full
  `simple debug doctor` output. Source presence alone proves neither available
  nor unavailable; an accidentally empty registry is also not truthful live
  evidence.
- **Adapters must not import an executable module with a top-level server
  call.** `HostDebugTarget` imported `SimpleDapSession` selectively, but the
  module still executed `simple_dap_server_main()` and polluted/hijacked doctor
  runs. Keep executable startup behind `fn main`; verify the Integration
  reproducer has no server-start side effect before accepting a live adapter
  probe.

- **All evidence is from the Rust seed.** Nothing here is self-hosted evidence.
- **CUDA and Vulkan genuinely run on device** — 20 launches each, field diffs
  clean.
- **Metal's entire device path is unverified.** `svmg_metal_kernel.metal` has
  never been compiled by any Metal compiler (no `xcrun`/`metal` on this Linux
  host). This is the feature's highest-risk unknown. Never state or imply that
  Metal works.
- **DAP GPU attach is ROUTING-ONLY.** No `.spl` → SVM-G path exists;
  `lower_svmg_program` is scoped to HIR test bodies with no caller outside
  `70.backend`. Filed:
  `no_general_spl_to_svmg_path_blocks_dap_gpu_attach_2026-08-09.md`.
- **The trait `with` sugar is INERT** — `desugar_traits` has no compile-path
  caller and the deployed seed predates the parser change.
- **`if val` is AOT-broken** (real `nil` → `SOME` under `native-build`), so a
  generated capability check would fail **OPEN** natively once wired.

## Testing practice this feature established

- **Assert on execution, not text or structure.** P0's generator passed 21/21
  while emitting code that could not compile.
- **A disjunctive spec is unfalsifiable.** "skip cleanly OR match ref_vm"
  proves nothing. Emit the branch (`DEVICE-RAN:` /
  `SKIPPED: … the DEVICE-RAN branch did NOT run`) and support
  `SIMPLE_REQUIRE_GPU=1`. Note `step()` text is **swallowed** on passing runs —
  use `print` or assert messages (found independently by N3 and P13).
- **Prove oracles by sabotage.** P6b's launch-count floor sabotaged to
  `expected 20 to be greater than 100000`; P4 caught its own zero-overhead
  oracle passing with guards removed.
- **Gate tautologies (P15).** 12 specs asserted only
  `test_env_require(...) == "blocked:..."` — green *because* the gate was shut,
  with false `@cover` claims. **The fix is NOT flipping the expected value to
  `ready`** — that trades one vacuous spec for another. Assert on behaviour
  behind the gate.
- **A green spec says nothing about reachability.** Three landed mechanisms
  have no caller: `desugar_traits`, `svmg_lowering`, `action_key`/
  `interface_digest`. Grep for callers before claiming end-to-end.
- **Treat evidence databases as checksummed artifacts.** Never repair their
  formatting by editing or trimming the serialized body: that invalidates the
  fail-closed CRC. Fix the owning serializer, make empty terminal fields
  explicit (`""`), then persist through the database owner and prove both
  whitespace cleanliness and checksum-based reload in System and Integration
  reproducers.
- **Offline inspection still owns a live service resource.** If an evidence
  command opens a temporary central session, record the operation outcome and
  close that session on both allowed and denied paths. A valid manifest and an
  authorization receipt do not prove lifecycle cleanup; compare active-session
  count before and after the production inspection path.
- **Cross-process probe bindings outlive in-memory service objects.** A CLI
  invocation must not recreate a probe merely to obtain an ID for removal:
  the new service instance can issue a different ID and leave the real backend
  breakpoint installed. Persist the original service-issued ID together with
  the adapter-native anchor, re-verify the durable adapter owner, authorize the
  removal in a fresh central context, remove the native probe, receipt the
  outcome, and clear the durable binding. Acceptance requires both the live
  backend apply/list/remove sequence and a zero-byte/absent binding afterward.
- **Interpreter adapters must call the landed debug facade, not redeclare
  externs.** The runtime-facing names are owned by
  `std.nogc_async_mut.io.debug_stubs` and may differ from an older backend's
  guessed `rt_debug_*` surface. Adapt semantic breakpoints, stack/locals, and
  cleanup through that facade; an unknown-extern failure is an adapter-owner
  defect, not evidence that interpreter debugging is unavailable. Also
  propagate a failed program run—receipts alone must not turn a non-executed
  fixture into a live-debug PASS.
- **Do not name a debug-test helper `context` when importing `std.spec.*`.**
  The SPipe/SSpec DSL exports its own `context`; ambiguous resolution can call
  that block helper and pass `nil` into a typed authorization path. Use a
  domain name such as `authorization_context` and retain the exact temporal
  policy spec so environment, privilege, and timestamp fields are exercised.
- **Never pass evidence-controlled paths through a shell.** Validate a bundle
  path as relative, bind it to an exact digest, and read bytes through the
  filesystem owner before decoding. Semantic replay may prove deterministic
  reproduction, but its receipt must keep the original defect status separate;
  successful parsing or replay is not evidence that the defect was fixed.
- **Keep each negative-path assertion with the scenario that produces it.** A
  misplaced assertion can make a valid rejection appear broken while leaving
  the intended invalid-input scenario oracle-free. For token receipts, assert
  negative-number rejection in the token case and calendar-shape rejection in
  the date case, then run the real CLI Integration boundary.

## Landed streams

P0 `50f06dcdd56` · P0b `8477ff5bdd0` · P1 `5ad3f64f928` · P2 `0b8ec4395b2` ·
P3 `79f3b662376` · P4 `a800bb04066` · P5 `abacef5d7f4` · P6 `7d53bf0a83b` ·
P6b `7f4004e1ff1` · P7 `40f72d2ceb1` · P8 `f94d2c2b02a` · P9 `6e108de66b2` ·
P10 `a4156a456d2` · P11 `2562958c4b0` · P13 `5fb82db579b` · P14 `c3307d1404d` ·
P15 `1bc53420716` · N3 `c2fc4ebaef5`

## Fix-verification contract (2026-08-18)

Every bug fix lands with: (1) a **reproduction spec run red-first** (observe
the reported symptom fail before the fix, report red→green with values);
(2) **similar-case specs** covering the sibling code paths that share the
defect's shape (other match arms, API-family twins, neighboring config axes,
boundary values — grep for the wrong pattern and cover each repeat);
(3) a **sabotage probe** (re-break → red → restore → green, all three
observed). Canonical wording: `.claude/agents/test.md` § "Every fix ships a
reproduction spec AND similar-case specs"; SPipe process hook:
`.claude/skills/spipe.md` § "Reproduce-first for bug-fix specs".

## Host-verified debug ladder (2026-09-05)

The canonical, command-by-command debugging order for this repo now lives at
[`.claude/skills/lib/debug_ladder.md`](../../../../.claude/skills/lib/debug_ladder.md)
(referenced from `.claude/agents/debug.md` and `.claude/agents/debug-analyst.md`).
Every command in it was executed on this host or is explicitly marked BLOCKED
with the reason — an aspirational debug guide is the failure mode it exists to
prevent.

Facts established while validating it against a real bug:

- **`gdb` is absent on this darwin/arm64 host; `lldb` is at `/usr/bin/lldb`** and
  is verified working against the seed binary. Do not write gdb recipes here.
- **Pick the tier by symptom.** lldb is for a native crash. For an *interpreted
  logic* bug (a wrong value) lldb tells you almost nothing — you are debugging
  the interpreter, not the program. Use a probe `.spl` that prints real values
  across the whole input domain. That is what actually found the defect below;
  reading the source did not, because the source is correct for ASCII.
- **Probe-script import gotcha:** `std.*` imports resolve anywhere, but `lib.*`
  imports resolve relative to the **probe file's own directory**, not cwd. A probe
  in `/tmp` silently cannot reach `lib.` modules.
- **Specs DO run on a bootstrap-only host** via
  `src/compiler_rust/target/bootstrap/simple run <spec.spl>`, which prints a
  `SPEC FILE VERDICT` line and a meaningful exit code. `simple test <spec>` does
  not exist on the seed. **Always read `executed=`** — `executed=0 failed=0` is a
  vacuous run, not a pass.
- **DAP / `simple debug` interpreter stepping remains BLOCKED** here: it needs the
  full self-hosted CLI, which is not deployed. T32 is likewise not wired — no
  `t32` server in `.mcp.json`, and the two scripts named in
  `doc/07_guide/app/tools/cli.md:277-279` do not exist.

Exercise outcome: walking the ladder on
`doc/08_tracking/bug/wire_to_bytes_returns_empty_2026-07-28.md` confirmed that
ticket FIXED, and the required generalization spec surfaced a **new** defect —
byte values >= 128 corrupt on wire round-trip because the wire text goes through
UTF-8-aware `text` concatenation. Filed at
[`doc/08_tracking/bug/wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05.md`](../../../08_tracking/bug/wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05.md)
with the reproduction spec GREEN and the generalization spec left RED, per
`.claude/rules/testing.md`.

## Producer/consumer split for debug evidence bundles (2026-09-05)

**Reader exists; writer does not — do not claim dump-based debugging works.**
The consumer side (`src/app/cli_debug/evidence_inspect_v1.spl` field-by-field
manifest validation, `src/app/cli_debug/evidence_replay_v1.spl` semantic
replay) is real and strict. Nothing in the repo produces a
`debug-evidence-bundle-v1` bundle — no coredump/minidump capture, no
ELF-core parser. The exact contract a future writer must satisfy, derived
from the reader with file:line citations, is pinned at
`doc/07_guide/app/debug/debug_evidence_bundle_contract.md`, with a
conformance spec at
`test/01_unit/app/cli_debug/debug_evidence_bundle_contract_v1_spec.spl`
(6/7 green; the 7th is correctly RED against a real, separately-filed reader
defect — `outcome.receipt_id` reads a field `DebugReceiptV1` does not have,
see `doc/08_tracking/bug/debug_evidence_inspect_receipt_id_field_missing_2026-09-05.md`).
The contract doc also carries the imported parser-safety policy (dump
artifacts are data, never executable; parsing is separately-allowlisted;
parser output is derived evidence with `parser_uid`/`parser_version`/
`derived_from`/`trust`; quarantine → hash → classify-by-content → scan →
parse; large dumps to a vault, never Git). What becomes possible once a
writer lands and the reader defect is fixed: R0 diagnose-from-dump (exact
build/session/capture identity, then semantic replay) without rerunning the
failing program — this is a target, not a landed capability, as of this
writing.

**Reader repaired 2026-09-05.** The `receipt_id` defect above is fixed:
`DebugReceiptV1` now carries `receipt_id`, issued by `service_v1.spl` as
`"receipt-<session>-<n>"`, and `service_v1.spl` also defines
`central_debug_service_v1_session_count()` (OPEN sessions only) and
`central_debug_service_v1_record_outcome(...)` (delegates to `_record`). The
policy constructors `debug_policy_observe_only_v1`/`_development_v1` live in
`service_v1`, not `contracts_v1` — import them from there.
`inspect_debug_evidence_bundle_v1` now completes end to end on a valid bundle:
contract spec 7/7, `evidence_inspect_v1_spec.spl` 5/5 on the bootstrap seed.
**Still non-compiling** and untouched: `src/app/cli_debug/probe_executor_v1.spl`
and `src/app/debug/interpreter_service_adapter_v1.spl`, which call
`central_debug_service_v1_apply_probe`, `_authorize_at`, `_record_at`,
`_receipts`, and reference `DebugProbeKindV1` / `DebugRootOperationV1.Probe` —
none of which exist. Contracts to settle first:
`doc/08_tracking/bug/debug_service_v1_probe_and_adapter_call_undefined_symbols_2026-09-05.md`.
Note also `test/fixtures/debug/evidence_bundle_v1` is NOT a valid bundle (no
artifact digest, no `receipts_digest`) — use `evidence_bundle_contract_v1`.

**Writer landed 2026-09-06 (Wave 2).** `src/app/cli_debug/evidence_write_v1.spl`,
`write_debug_evidence_bundle_v1(root, build_id, artifact_paths)`; CLI
`simple debug write <root> --build-id sha256:<hex> <artifact>...`. Copies existing
files into `<root>/artifacts/` and emits `manifest.sdn`, `receipts.sdn` (the
authorize+record pair of one `Evidence`/`Passive` `write-bundle`) and
`normalized/state_capsule.sdn`; output is accepted by
`inspect_debug_evidence_bundle_v1` (`evidence_write_v1_spec.spl` 5/5, seed).
NOT done: no core/minidump/trace CAPTURE, no ELF-core parser, no capability above
`Unverified` — a bundle proves identity and integrity, never replayability.

## Lane docs (2026-09-05)
- design: `doc/05_design/app/debug/debug_capability_truth_wave0_design.md` · plan: `doc/03_plan/app/debug/dump_replay_wave_plan.md` · state: `.spipe/debug_capability_truth_wave0/state.md` · receipt contract: `doc/07_guide/app/debug/state_capability_receipt_contract.md`

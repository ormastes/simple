# Ordinary CLI streaming request could silently retain every parser module

Status: source fix and focused native regression PASS; producer rebuild and
full CLI memory replay pending. This is not a production verification PASS.

## Evidence

The diagnostic full CLI build under
`/mnt/simple-bootstrap-6b2/linux-early-phase3-908-20260930/phase2-cli-fix3-attempt1`
used producer SHA-256
`9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`,
entry `src/app/cli/_CliMain/main_and_help.spl`, frontend cache disabled, and an
explicit `SIMPLE_STAGE3_STREAMING_SURFACES=1` override. Its recorded environment
does not include `SIMPLE_BOOTSTRAP`; effective inherited environment attribution
must be established separately if the launch environment was not exhaustive.

The log reached legacy `phase=parse done=2064 total=2493`, then shell PID
690815 was killed with exit 137. These progress receipts are emitted by the
legacy parser loop. The streaming loop emits module-surface release receipts.
At 10:24:04 KST, the kernel reported global OOM and killed kernel PID 17260,
`simple.rejected`, with anonymous RSS 17,355,696 KiB and virtual size
17,396,708 KiB. Timing correlates the events; the namespace PID mapping was not
captured and is not claimed as proven.

`driver_streaming_surface_enabled` required both the explicit request and
`SIMPLE_BOOTSTRAP=1`. Consequently an otherwise valid ordinary AOT entry with
the explicit request alone selected `parse_all_impl`. That path retains rich
`ParserModule` boxes for all unique sources; its parse calls are outside the
driver's per-file transient scope. Streaming instead projects and promotes the
compact surface, ends the parser scope, resets parser globals, and later
reparses bodies for HIR. This is a source-proven route/lifetime difference,
not proof that every retained allocation is an unbounded leak.

## Fix

Explicit Stage 3 streaming requests no longer require bootstrap mode. The
existing Stage 4 flag pair remains a valid explicit request. The pure route
policy retains AOT, entry authority, coverage, MC/DC, and VHDL constraints.
Default/off requests keep the legacy route. A blocked explicit request returns
a specific `E-DRV-STREAM-*` error before source loading, rather than silently
selecting retain-all parsing. Ordinary compilation semantics and the streaming
parser implementation are unchanged.

The orchestration layer uses the checked route for initial source ownership.
The parse and HIR dispatch predicates call the same policy. No allocator,
resource cap, process termination, runtime host helper, or cache content changes
are included. The frontend borrowed-scope fix is an independent prerequisite
for enabling frontend caching with streaming on the old producer lineage.

## Validation and limits

`test/fixtures/compiler/ordinary_streaming_route/main.spl` built natively with
the self-hosted producer, `SIMPLE_NO_STUB_FALLBACK=1`, bootstrap disabled, and a
private cache. All 22 route/default/guard/diagnostic checks passed, exit 0.
Exactly two source modules compiled. Compile: 23.07 s, maximum RSS 547,532 KiB.
Execution: below 0.01 s, maximum RSS 1,400 KiB. These numbers describe the small
regression only and are not a full compiler memory comparison.

Evidence is under `/mnt/simple-bootstrap-6b2/cli-memory-route-fix-20260930`:
`plan.json`, `compile.log`, `compile-time.txt`, `run.log`, `run-time.txt`.
The first attempt exposed negative integer match-arm MIR error B5b, recorded
separately; the second compiled and linked successfully. No green test was
repeated. `ordinary_streaming_request_spec.spl` additionally describes the
driver wiring and rejection-before-load contract; the full SPipe runner was
not launched in this resource-constrained diagnostic lane.

No rebuilt driver integration run, optimizer-app run, whole compiler/lib/MCP
checks, or complete CLI memory replay was performed. Before deployment, rebuild
the producer with this patch, run the SPipe wiring spec, and replay the same
frozen CLI closure with the same cache policy. Require streaming release
receipts, successful complete compilation, and peak RSS measurement. This
patch does not fix the separate HIR/symbol snapshot retention in builds that
already selected streaming.

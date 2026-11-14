# Spliced std.spec bodies resolve framework internals against the entry spec module

Date: 2026-11-14
Branch observed: `release/1.0.0` @ `76f3263aa71`
Host: Windows (Git Bash), seed runtime, `--mode=interpreter`

## Symptom

Heavy integration specs that DEMOTE to the seed's `hybrid-interp-splice`
engine fail every test with e.g.:

```
semantic: test/02_integration/app/devhub/messenger/devhub1_oss_interop_spec.spl:652:5:
function `_aggregate_active` not found
```

(The reported file/line is the ENTRY spec, but the line number — past the end
of the file — is inside the spliced body of `std.nogc_sync_mut.spec.skip`,
whose real source line is `src/lib/nogc_sync_mut/spec.spl:652`.)

Confirmed on `devhub1_oss_interop_spec` (17/17 fail) and
`sqlcipher_session_boundaries_spec` (same class, though that instance was
unblocked by publishing `sqlcipher4_error_code`, a separate privatization).

## Root cause (verified by experiment)

1. `skip`'s body (and the other framework entry points) call module-internal
   helpers: `_aggregate_active`, `_aggregate_declare`, `_aggregate_enum`,
   `_aggregate_result`, `_active_assurance_profile`, `_reject_skip`,
   `validate_free_text_skip`, `_run_test`, ...
2. When the JIT demotes (`[engine-demotion] reason=hybrid-interp-splice`),
   these bodies are spliced (inlined) into the ENTRY spec module.
3. The spliced body's symbol references resolve against the ENTRY module's
   import table — NOT against the callee's home module bindings.
4. The entry spec imports the framework via `use std.spec.*`; the wildcard
   does not bind underscore-prefixed names (verified: an explicit named
   import `use std.spec.{_aggregate_active}` moved the failure to the next
   internal, `_run_test`; repeating the import for the whole chain is the
   only spec-side unblock, and it effectively makes framework internals
   public API through every spec's import list).

Specs whose closures compile under the JIT (no demotion) never splice and
pass; that is why lighter unit specs are unaffected and the failure is
specific to heavy closures on the seed runtime (missing `rt_linux_group_*`
and related runtime symbols force the demotion on Windows).

## Why not fixed here

- Making the wildcard import bind underscore names is a compiler semantics
  change; risky to land mid-bootstrap.
- Enumerating the internals in every heavy spec pollutes the spec surface
  and freezes framework internals as accidental public API.
- The stage-2/stage-3 self-hosted compiler does not demote on this host
  (its runtime provides the spliced symbols), so the same specs are expected
  to pass there — verify with:
  `SIMPLE_MCP_TEST_BINARY=<self-hosted> bin/simple test test/02_integration/app/devhub/messenger/devhub1_oss_interop_spec.spl --mode=interpreter`

## Correct fix (for the compiler lane)

Bind spliced-body symbol references against the CALLEE module's bindings
(carry the home module's import context through the splice), so framework
internals stay internal regardless of how the entry module imports the
framework. File against the hybrid-interp-splice lowering in
`src/compiler` (HIR lowering / MIR splice path).

## Related

- `doc/08_tracking/bug/smux_capture_pane_merged_history_2026_11_12.md`
  (same class: check requires capabilities the current runtime lacks)
- `#9061` republished the spec-framework aggregate internals and re-exported
  them through the `nogc_async_mut` spec shim — necessary but not sufficient;
  the wildcard still does not bind them into the entry module.

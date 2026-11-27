# Entry-closure scanner drops every import after a multi-byte UTF-8 line on self-hosted runtimes (substring-policy probe misdetection)

- **Status:** ROOT-CAUSED + SOURCE FIX LANDED 2026-11-13 (PR #8780, commits
  `8c4c44c4cc0` fix + `9e30cee6dcc` tracking on
  `work/closure-scan-substring-policy-probe-20261113`)
- **Severity:** P1 — silently wrong entry closures; poisoned stage-2 matrix rows
- **Component:** `src/compiler/80.driver/driver_entry_closure_core.spl`
  (`_driver_substring_is_byte_based_v1`, 2026-11-11 byte/char defense block)
- **First observed:** stage-2 verification matrix, pin `47e28950755a`
  (2026-11-13), rows `compiler_cli_build` (241 errors / 21 poisoned modules)
  and `test_runner_build` (newly failing)

## Symptom

Stage-2 matrix `compiler_cli_build` fails phase 3 with ~160 unique
`missing module surface for <module>` victims (241 errors total); the victim
modules (`app.t32_cli.bridge`, `app.devhub.cmd_jira`,
`std.nogc_sync_mut.io.debug_stubs`, `nogc_async_mut.sosix.host_facade`,
`app.watch.runner`, ...) were **never parsed in phase 2** — zero
`phase2:surface:file:*` events for their paths in the row log, and the
`[parse-closure] parent_walks=1 selected=2188` line shows the coordinator's
closure walk itself dropped them. `test_runner_build` fails with 16
overlapping victims; its `mir-shard ... no module verdict ... refusing the
unbounded unsharded fallback` line is a **consequence** (the shard frontend
records the 241 HIR errors, the owner goes BLOCKED before publishing verdicts,
and policy refuses the in-process fallback), not an independent defect.

The victim set varies with tree/closure state (2026-11-12 runs victimized
`src/app/t32_cli/*` and `src/lib/editor/services/*`; 2026-11-13 runs
victimize io/watch/sosix/devhub modules) — because it depends on **which
source files contain a multi-byte UTF-8 character before their import
block**, not on any fixed module set.

## Root cause (proven by minimal probes, 2026-11-13)

The 2026-11-11 multi-byte defense
(`doc/08_tracking/bug/entry_import_scanner_loses_imports_after_multibyte_utf8_2026-11-11.md`,
commit `65f92308bc3`) detects the runtime's substring unit policy by comparing
`rt_bytes_to_text([0xC3, 0xA9]).substring(0, 1)` against
`rt_bytes_to_text([0xC3])`:

```
_g_substring_policy = if probe_txt.substring(0, 1) == first_byte: 1 else: 0
```

`[0xC3]` is **invalid UTF-8** (a lone lead byte). Measured on the pinned
stage-2-admitted binary (`ab1501fe…`, aarch64-apple-darwin, llvm):

```
one = rt_bytes_to_text([0xC3])  -> bytes 239 191 189   (U+FFFD, 3 bytes)
e.substring(0,1).byte_len()     -> 1  (substring IS byte-based here)
e.substring(0,1) == one         -> false  => policy misdetected as "char-based"
```

The UTF-8-validating pure-Simple runtime replaces the lone 0xC3 with U+FFFD,
so on every self-hosted (byte-based) runtime the probe concludes
"char-based". The scanner then takes the char-conversion path
(`_driver_byte_to_char_advance_v1` + char-index `substring`) on a runtime
whose `substring` is byte-based: line slices after the first multi-byte
character are desynced, the `use `/`export ` prefix match fails, and **every
import after the first multi-byte line is silently dropped from the entry
closure**. The 2026-11-11 verification was seed-smoke only ("All runs:
`SIMPLE_BINARY=$PWD/bin/simple.exe`"), so the misdetection on self-hosted
runtimes was never exercised.

Minimal closure-walk repro (stage-2 binary, `SIMPLE_SCV_FREEZE_FALLBACK=1`,
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`, 15-sibling import block copied from
`src/app/devhub/main.spl`, whose line 1 carries an em-dash):

- em-dash header: `[parse-closure] selected=2` — only the first import bound;
  14 sibling imports silently skipped.
- same file with the em-dash replaced by `-`: `selected=16` — all 15 bind.
- 2-byte (`é`) header reproduces identically; multi-byte char AFTER the
  import block does not affect it.

The pure-Simple runtime text primitives themselves are correct on this lane
(byte_at/byte_len/substring all byte-based; verified byte-by-byte with
`rt_bytes_to_text` round-trips) — this is purely the probe's reference-text
assumption.

## Fix

`_driver_substring_is_byte_based_v1` now distinguishes the policies by the
slice's **byte length** — `probe_txt.substring(0, 1).byte_len() == 1` —
with no second probe text at all. `byte_at`/`byte_len` are byte-based on
every documented lane (both 2026-11-11/11-12 records agree), so:

- byte-based runtime: substring(0,1) = single byte 0xC3 → byte_len 1 → policy 1.
- char-based runtime (Rust seed): substring(0,1) = whole 2-byte char →
  byte_len 2 → policy 0.

## Impact

- Explains the persistent post-#8728 `missing module surface` family: the
  codec fix removed the HIR-cache store refusals (zero in the 11-13 log),
  and the residual victims are the closure-scan drop documented here.
- The C7 "shard-index export-drop" suspect
  (`cold_hir_compiler_publication_v1.spl`) is exonerated for this failure
  mode: the victims were never parsed, never committed, never exported.
- Any self-hosted build over sources with non-ASCII comments/docstrings
  before import blocks gets a silently shrunken closure.

## Verification

- Minimal closure-walk repro (stage-2 binary, `SIMPLE_SCV_FREEZE_FALLBACK=1`,
  `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`, 15-sibling import block copied from
  `src/app/devhub/main.spl`, whose line 1 carries an em-dash): em-dash header
  `[parse-closure] selected=2` (only the first import bound, 14 skipped);
  same file ASCII `selected=16` (all 15 bind); 2-byte (`é`) header reproduces,
  multi-byte after the import block does not affect it.
- Byte-level runtime probes on the pinned binary: `rt_bytes_to_text([0xC3])`
  → bytes 239 191 189 (U+FFFD); `e.substring(0,1).byte_len()` → 1 (substring
  IS byte-based here); `byte_at`/`byte_len`/byte-slices exact.
- Decisive A/B: a verbatim extraction of the scanner pipeline
  (`_driver_entry_import_module_paths_text_fallback` and its helpers, copied
  mechanically from each tree; `_pp_preprocess_conditionals` → identity,
  valid because probe contents carry no directives) compiled by the FROZEN
  stage2 binary and run on the stage2 runtime, identical except for the probe
  function:
  - base (`47e28950755`): case1 em-dash-before-imports → 0 imports (all
    dropped); case3 multi-byte between imports → first import only;
    ASCII control → 2. SCANNER-FAIL (exit 1).
  - fix (`8c4c44c4cc0`): 3 / 2 / 2 on the same three cases. SCANNER-OK
    (exit 0).
  (Importing the whole real module for the A/B is impossible on the frozen
  binary: its own buggy walk shrinks the probe build's closure and both trees
  die with the same 4286-error missing-surface cascade — the matrix failure
  in miniature.)
- End-to-end matrix verification is pending the next stage-2 admission (the
  admitted binary predates the fix; only a compiler built FROM these sources
  scans correctly on self-hosted runtimes). Exact command:

```
sh scripts/bootstrap/lib/verify-stage2-compiler-tests.shs \
    <output-dir> aarch64-apple-darwin <stage2-candidate> <candidate-sha256>
```

(the mandatory stage-2 compiler-test matrix invoked by
`scripts/bootstrap/run-managed-from-admitted.shs`; the
`compiler_cli_build` and `test_runner_build` rows must leave the
missing-module-surface family).

## Relation to prior records

- 2026-11-11 scanner doc: same symptom family, seed-side root cause fixed
  and routed; the driver-side defense added there carries this defect.
- 2026-11-12 matrix doc: the fixed victim set observed there was the SAME
  mechanism (its "commit-done then dropped" reading was compounded by the
  concurrent codec refusals); the "independent surface-registry/closure gap"
  predicted there is this bug.
- `substring_units_differ_by_execution_lane_2026-11-12.md`: the probe did
  not disagree about the unit — it disagreed about the reference text.

# Obsolete-spec classification — decision package (2026-08-11)

**Status: EVIDENCE ONLY. Nothing in this repo was deleted while producing this
doc.** All deletion decisions below are recommendations for the user to act
on (or not) — no automated cleanup follows from this file.

## Provenance note — the "202 wholly-obsolete" list could not be located

`grep -r "obsolete" doc/08_tracking/ doc/09_report/` and a search for "202" +
"wholly" turned up no prior report enumerating exactly 202 wholly-obsolete
specs. The closest documented artifacts are:

- `doc/08_tracking/bug/landed_specs_import_modules_absent_from_origin_main_2026-08-08.md`
  — 122 tracked spec files (68 unique basenames) whose `use std.<module>`
  target does not exist anywhere on `origin/main`, resolved by a
  file-existence oracle calibrated 22/22 (11 known-good / 11 known-bad) and
  explicitly corrected for the `src/std` symlink-blob false-positive trap.
  **That same doc's own conclusion: zero deletion history for any of the 85
  untriaged basenames** (`git log --diff-filter=D` empty for every one
  checked) — i.e. these are unlanded/planned-but-never-shipped work, not
  code that regressed. The doc's verdict was "leave, do not delete."
- `doc/08_tracking/bug/specs_assert_against_nonexistent_product_paths_2026-08-10.md`
  + `doc/08_tracking/test/spec_missing_path_census_2026-08-10.tsv` — 2,002
  `<spec>\t<missing product path>` rows (776 unique spec files) where a spec
  reads a path absent from the committed tree and a **negative** assertion
  (`to_equal(false)` / `not .contains`) passes vacuously against the empty
  read. This is a different mechanism from missing `use` imports: it's a
  fixture/read-path miss, not an unresolvable module.

Per the task's fallback instruction, this doc reconstructs a conservative
candidate set from these two enumerated, evidence-backed corpora rather than
inventing a new sweep. Total candidate pool examined: **122 (import-absent)
+ a sampled slice of the 776 (fixture-path-absent)** = evidence for both the
SUBJECT-GONE and VACUOUS buckets below. DUPLICATE and STILL-LIVE are sampled
from the wider corpus for contrast/control.

## Buckets

### SUBJECT-GONE — 122 candidates (evidence: import target absent from origin/main)

Source: full list in `landed_specs_import_modules_absent_from_origin_main_2026-08-08.md`
("Flagged specs" section). Each cites `<spec path> -> <missing std.* import>`.
Sample (first 10 of 122):

- `examples/10_tooling/mate_broker/test/dashboard_ui_spec.spl` -> `std.ui.`
- `test/01_unit/app/llm_caret/messaging/caret_command_spec.spl` -> `std.test.`
- `test/01_unit/app/tooling/ds_utils_spec.spl` -> `std.ds_utils.`
- `test/01_unit/app/tooling/probability_utils_spec.spl` -> `std.probability_utils.`
- `test/01_unit/compiler/diagnostic_formatter_contract_spec.spl` -> `std.diagnostics.formatters.`
- `test/01_unit/compiler/linker/linker_wrapper_smf_spec.spl` -> `std.system.`
- `test/01_unit/compiler/linker/object_emitter_spec.spl` -> `std.system.`
- `test/01_unit/compiler/parser/treesitter_lexer_real_spec.spl` -> `std.parser.treesitter*`
- `test/01_unit/compiler/parser/treesitter_parser_real_spec.spl` -> `std.parser.treesitter*`
- `test/01_unit/hal/hal_traits_spec.spl` -> `std.bare.hal.*`

**IMPORTANT CAVEAT (carried over from the source doc, do not drop when
acting on this bucket):** `git log --diff-filter=D` is empty for every
top-level namespace in this set (`blink`, `cc`, `parser.treesitter`, `bare`,
`sys`, `signature`, `probability_utils`, `plugin`, `game_engine`, `file`,
`ds_utils`, `diagnostics`, `collection_helpers`, `prelude`, `doctest`, `app`,
`test/helpers`, `tooling/compiler`, `debug/remote`, `gc_async_mut.*`). None of
these modules were ever landed and later deleted — they are specs written
ahead of unlanded implementation ("red-phase"/planned work), not specs whose
subject regressed away. **This is SUBJECT-GONE only in the literal sense
"import target absent at origin tip"; it is NOT evidence the intended
capability was abandoned.** Recommended action below reflects that
distinction.

### VACUOUS — sample of 12 (from 776 unique specs in the missing-path census)

Source: `spec_missing_path_census_2026-08-10.tsv`, pattern documented in
`specs_assert_against_nonexistent_product_paths_2026-08-10.md` — a spec reads
a product path absent from the tree, then a **negative** assertion against
the resulting empty content passes vacuously (positive assertions on the same
miss fail loudly, which is why this shape survives).

- `test/02_integration/app/remote_test_log_modes_spec.spl` — missing-path ref
- `test/01_unit/app/test_daemon/test_daemon_cache_spec.spl` — missing-path ref
- `test/unit/app/debug/remote/dwarf_spec.spl` — missing-path ref
- `test/unit/os/qemu_runner_tool_validator_spec.spl` — missing-path ref
- `test/02_integration/remote_jit/ch32v307_composite_runner_spec.spl` — missing-path ref
- `test/unit/app/tooling/test_db_performance_spec.spl` — missing-path ref
- `test/integration/app/llm_process/llm_process_gen_spec.spl` — missing-path ref
- `test/system/compiler/rtl_mdsoc_plugin_stubs_spec.spl` — missing-path ref
- `test/01_unit/app/mcp_unit/transport_tcp_spec.spl` — missing-path ref
- `test/01_unit/app/io/cli_argv0_resolution_spec.spl` — missing-path ref
- `test/unit/os/memory/mold_linker_spec.spl` — missing-path ref
- `test/01_unit/app/mcp_unit/fileio_protection_spec.spl` — missing-path ref

Exact missing path per file is in the tsv (col 2); not hand-verified here as
genuinely-vacuous (i.e. whether the assertion touching that path is negative)
for each of the 12 — that requires opening each spec body, which was out of
budget this pass. **Do not treat this bucket as verified-vacuous; treat it as
"matches the documented missing-path pattern, needs a body read before any
action."**

### DUPLICATE — 0 confidently identified this pass

The known `test/01_unit/**` vs `test/unit/**` (and `test/02_integration` vs
`test/integration`, `test/03_system` vs `test/system`) mirror is the
documented, intentional duplication (`test_tree_divergence_baseline.txt`) and
is explicitly **excluded** per the task brief — it is not evidence of
obsolescence. Beyond that mirror, no semantic-duplicate pairs were confirmed
in this pass (would require diffing spec bodies, not just paths/imports,
which was out of budget). **Recommended action: do not treat 0 as "none
exist" — it means unexamined, not clean.**

### STILL-LIVE — sample of 12 (control group, from specs absent in both flagged corpora)

Drawn at random from the 18,789 spec files (of 19,684 total) that appear in
neither the SUBJECT-GONE list nor the missing-path census — i.e. no detected
import or fixture-path miss:

- `test/unit/std/improved/uuid_integration_spec.spl`
- `test/01_unit/compiler/hir/hir_forward_lowering_spec.spl`
- `test/03_system/os/os_filesystem_variants_spec.spl`
- `test/01_unit/compiler/coverage/branch_coverage_20_spec.spl`
- `test/system/stress_7_system_spec.spl`
- `test/03_system/core/error_path/error_path_74_system_spec.spl`
- `test/unit/lib/common/base_encoding/base64/base64_spec.spl`
- `test/03_system/core/error_path/error_path_40_system_spec.spl`
- `test/unit/app/complete/install_1_complete_spec.spl`
- `test/01_unit/app/cli/query_outline_domain_blocks_spec.spl`
- `test/01_unit/lib/common/ui/theme_notification_protocol_spec.spl`
- `test/01_unit/std/improved/slice_unit_spec.spl`

These are **KEEP** by default per the task's "err toward STILL-LIVE when
unsure" instruction — no evidence of a missing subject was found for any of
them in either corpus.

## Runtime verification — INVALIDATED, not skipped

The task asked for a 10+10 `bin/simple test` sample verification (SUBJECT-GONE
vs STILL-LIVE). This was attempted on 8 SUBJECT-GONE files and 3 STILL-LIVE
control files; **all 11 timed out identically at 15s with the same generic
`simple migrate --fix-generics` output**, with zero discriminating signal
between the two buckets. Root cause: `readlink -f bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple`, and `bin/simple --version`
prints `WARNING: this Rust-built Simple binary is a bootstrap seed only; do
not use it as the normal tool.` — the deployed binary is currently the
**seed**, not the self-hosted pure-Simple binary the repo's own rules say all
`test` runs must use. This is a harness-availability defect discovered
mid-task, not a per-spec finding, and it means **no execution-based evidence
was obtainable in this pass for either bucket** — consistent with the task
brief's own caution that run-based checks are fail-open here and that static
path-existence evidence should be primary. Static evidence (git-tree
existence of imports / fixture paths) is what backs every classification
above; no bucket rests on a `bin/simple test` result.

## Counts

| Bucket | Count (this pass) | Confidence |
|---|---|---|
| SUBJECT-GONE | 122 candidates (full enumerated list, source doc) | Path-existence verified (22/22 calibrated resolver); "abandoned capability" interpretation NOT verified — no deletion history found for any of them |
| VACUOUS | 12 sampled (of 776 unique specs matching the pattern) | Pattern-matched only; per-file negative-assertion body read NOT done |
| DUPLICATE | 0 confidently identified | Not examined beyond excluding the known mirror trees |
| STILL-LIVE | 12 sampled (of 18,789 candidates with no detected miss) | Absence-of-evidence only; not individually opened |

## Recommended actions (decisions for the user, not taken)

1. **SUBJECT-GONE (122):** Do NOT bulk-delete. The source doc's own
   deletion-history check found these are unlanded/planned work, not
   regressions — deleting them destroys planned coverage rather than removing
   dead weight. If the user wants cleanup here, the correct action is likely
   "land the missing modules" or "explicitly re-scope/park the spec with a
   tracked TODO," not deletion. A grandfathered pre-push guard was
   recommended but not landed by the source doc — still open.
2. **VACUOUS (776 pool, 12 sampled):** Needs a second pass that actually
   opens each spec body to confirm the assertion touching the missing path is
   negative (this pass only confirmed path-absence, the necessary but not
   sufficient condition). Do not delete on path-absence alone.
3. **DUPLICATE (0 identified):** No action — bucket is unpopulated in this
   pass, not proven empty. A real duplicate sweep needs body-level diffing,
   out of this pass's budget.
4. **STILL-LIVE (18,789 pool, 12 sampled):** Keep. No further action.

## Runtime provenance at time of this analysis

```
$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

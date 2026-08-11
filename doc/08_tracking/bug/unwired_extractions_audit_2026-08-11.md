# Unwired-Extraction Audit — dedup authored, never wired (2026-08-11)

**Status: OPEN (audit only — nothing wired this session; see "Why nothing was wired")**

## Pathology

A deduplication/extraction is AUTHORED, sometimes announced as Resolved, and then
**never wired to a consumer**. The duplicates it was meant to replace keep
breeding underneath it. It survives because the dead extraction has **no specs**,
so nothing fails when it is orphaned. **Silence reads as health.**

A "Resolved" banner is not evidence. Instance 3 below carried a *re-verified*
banner over a dead file for three months.

## Method + fail-open warnings

- All censuses used `/usr/bin/grep -rn` unrestricted. The wrapped `grep` is ugrep
  honouring `.gitignore` and **under-reports**.
- Positive control for every absence check: `/usr/bin/grep -rln 'format_utils'
  --include=*.spl src` → 6 files; `ls src/lib/hardware/` → non-empty. Scans reach
  the tree.
- **An unresolved `use` only WARNs.** "Zero importers" is therefore FAIL-OPEN as a
  deletion criterion. Nothing below is marked deletable. Sibling preloading can
  keep a file live with zero `use` anywhere.
- `src/compiler_rust/` is a **symlink**; `/usr/bin/grep -r` does not descend it.
  Entries under it were checked separately and are flagged as lower-confidence.
- `build/**` and `.claude/worktrees.pre_migrate_backup/**` are snapshots, not live
  source. Hits there prove history, not wiring.
- **A path-scoped grep is fail-open against renames.** One finding in this audit
  (instance 4) was initially called a false-Resolved purely because the directory
  the doc named no longer existed — the work had in fact landed one rename away.
  Never conclude "the claimed wiring is absent" from a missing path; confirm by
  searching for the extraction's **symbols** tree-wide.

---

## Confirmed instances

### 1. `src/os/kernel/arch/common/` — Wave 2 AC-3 helper extraction (2026-04-25)

10 helpers extracted; zero importers until 2026-08-10. **Now PARTIALLY wired** —
`cstart_bridge`, `entropy_mix`, `gic_common`, `canary_state` have real per-arch
importers (arm32/arm64/riscv32/riscv64).

**Still ZERO importers** (exported from `mod.spl`, so re-export masks the orphan):
- `paging_walker.spl`
- `sbi_shim.spl`
- `timer_math.spl`

Live duplicates: the per-arch paging/timer/SBI copies these were extracted from
remain live under `src/os/kernel/arch/{arm64,riscv64,x86_64}/`.
**No spec covers any of the 10.**

Wiring step: replace the per-arch paging-walk / timer-divisor / SBI-ecall bodies
with imports of the three modules, one arch at a time.
**Blocked this session:** verification requires a SimpleOS kernel build, which is
explicitly off-limits (six sessions contending on the shared tree).

### 2. `config/mcp/mcp_startup_lib.shs` — 388 lines, ZERO executable references

Only references: its own line 6 usage comment (which names a nonexistent `.sh`,
not `.shs`), and four doc files. **Zero hits in `bin/**`, `scripts/**`,
`config/mcp/install.shs`, `config/mcp/install.ps1`, or any `.mcp.json`.**

Companion orphan: `src/compiler_rust/lib/std/src/mcp/mcp_common.spl` — 2
importers, **both intra-package** (`mcp/__init__.spl:17` re-export,
`mcp/advanced.spl:5`). No `src/app/**` consumer.

**Live duplicates: JSON-RPC/stdio Content-Length framing is implemented at 20+
distinct sites**, including `src/app/mcp/main_transport.spl`,
`src/app/lsp_mcp/main.spl:184`, `src/app/simple_lsp_mcp/json_helpers.spl:355`,
`src/app/mcpgdb/{json_helpers.spl:259,backend_common.spl:275}`,
`src/app/md_lsp/md_lsp_main.spl:107`, `src/app/dap/simple_dap_main.spl:303`,
`src/app/llm_caret/messaging/mcp/protocol.spl:60`, `src/app/svim/lsp_client.spl:117`,
`src/lib/nogc_sync_mut/{mcp_sdk/transport/stdio.spl:70,lsp/lsp_protocol.spl:53}`,
`src/lib/nogc_async_mut/mcp/{protocol.spl:77,lazy_protocol_io.spl:60}`, plus
vendored copies under `examples/`.

**Precedent that dedup here is achievable:** `src/lib/{nogc_sync_mut,nogc_async_mut,
gc_async_mut}/{lsp,dap}/transport.spl` are already 2-line shims delegating to
`std.editor.services.lsp_transport`, and that path HAS spec coverage.

**No `*_spec.spl` matches `mcp_common` or `mcp_startup_lib`** — both untested.

Wiring step (smallest, ordered): convert `src/app/mcpgdb/json_helpers.spl:259-271`
and `backend_common.spl:275-307` into shims over
`std.editor.services.lsp_transport`, mirroring the existing 2-line delegation.
Do NOT start with `mcp_common.spl`/`mcp_startup_lib.shs` — wiring an untested
orphan is unverifiable until a spec exists. Either wire `mcp_startup_lib.shs`
into the launchers or delete it, but only after a launcher smoke test exists.

### 3. CSS colour commonization — FALSE "Resolved", with corrections

`doc/08_tracking/bug/browser_color_commonization_blocked_2026-05-10.md` —
`Status: Resolved (2026-05-19)`, re-verified 2026-05-29.

Corrections to the original report, established this session:
- The surviving extraction is **`src/lib/common/color/css.spl`**, not
  `gpu/browser_engine/css.spl`.
- The doc also cites `src/lib/gc_async_mut/web/css_named_colors.spl` — **that file
  does not exist.**
- `src/lib/common/color/` has **no `__init__.spl` at all**, so "absent from the
  export list" was a mis-diagnosis: consumers import leaf modules directly
  (`use std.common.color.types`, `.convert`), and that mechanism works.
- **`css.spl` now HAS a spec**: `test/01_unit/lib/common/color/css_color_spec.spl`
  imports `std.common.color.css.{parse_css_color, named_color, parse_hex_color}`.
  So it is reachable and tested — but has **zero production consumers**.
- `CssLength` / `css_px_*` exist **only** in `build/**` snapshots and
  `.claude/worktrees.pre_migrate_backup/**`. They are gone from live source.

**Live duplicates that the extraction never replaced** (all `u32`-typed):
`src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl` (`parse_color_value:8`,
`parse_hex_color:95`, `named_color_to_u32:632`),
`simple_web_html_layout_renderer_foundation.spl` (`parse_color:1107`,
`parse_color_any:1137`, `parse_color_alpha:1184`),
`simple_web_engine2d_renderer.spl` (`_hex_color_at:245`),
`simple_web_css_box_effects.spl` (`_box_shadow_hex_color:282`),
`style/supports.spl` (`_supports_hex_color:427`).

**Root cause of the non-wiring — the load-bearing finding:** the extraction
returns `Color?` (a struct); every live browser consumer is `u32`-typed. The
commonization was authored against the wrong type, so no call site could adopt it.
An adapter (`Color -> u32`) is required before any wiring is possible.
Verdict: **the Resolved banner is false and should be reopened.**

### 4. `doc/08_tracking/bug/rv32_rv64_rtl_unification_results_2026-07-21.md` — NOT false; STALE PATH only

**This was initially mis-triaged as the worst false-Resolved in the audit. It is
not. Recorded here in full because the mis-triage is itself the most instructive
result of this session.**

The doc claims (line 3) *"Status: COMPLETE — Merge executed, compilation
verified"*, with 8 unified templates in `src/lib/hardware/riscv_rtl/common/` and a
quoted passing `bin/simple check src/lib/hardware/riscv_rtl/common/`.

`src/lib/hardware/riscv_rtl/` indeed **does not exist**, and a path-scoped grep
returns zero — which reads exactly like instance 3. **It is a false negative.**

The unification actually landed at **`src/lib/hardware/riscv_common/`** (19 `.spl`
files: `rtl_pkg.spl`, `rtl_decode.spl`, `alu.spl`, `decode.spl`, `csr_defs.spl`,
`registers.spl`, `xlen.spl`, …) and is **genuinely wired**, with real cross-module
importers:
- `src/lib/hardware/rv32i_rtl/decode.spl:16-17` → `riscv_common.rtl_decode`
- `src/lib/hardware/rv32i_rtl/pkg.spl:19-20` → `riscv_common.rtl_pkg`
- `src/compiler/70.backend/backend/riscv_target.spl:6` → `riscv_common.pkg.riscv_linux_pkg`
- `src/lib/hardware/rv32gc/top/rv32_machine.spl:1`, `fpga_linux/riscv_fpga_linux.spl:33`
- `src/lib/nogc_{sync,async}_mut/debug/remote/exec/adapter_ghdl_rv32.spl:16`

It also **has a spec**: `src/lib/hardware/riscv_common/test/riscv_common_xlen_mask_spec.spl`.

Verdict: **NOT a false-Resolved.** Only the doc's directory name is stale (the
tree was renamed `riscv_rtl/common/` → `riscv_common/` after the doc was written).
Action is doc-only: correct the paths. Same class as instance 5.

**Method lesson — this is the important part.** Grepping for the *path* a doc
claims is fail-open in the presence of a rename: absence of the path proves
nothing about absence of the work. Every "claimed file is missing" finding must be
followed by a **symbol-level** search for the functions the extraction provides,
across the whole tree, before the doc is called false. Instance 3 survived that
second test (its symbols really have zero production consumers); this one did not.
Two sibling directories, `riscv_rtl/common/` and `riscv_common/`, differ by a
transposition — precisely the shape that defeats a path grep.

### 5. `doc/08_tracking/bug/lexer_position_unification_2026-07-29.md` — stale, NOT false

The fix half is genuinely wired (`lex_token_end_get` 7 files, `lex_live_line_get`
and `lex_force_set_pos` 3 files each). Only the disposition table is stale: it
says the dead cluster `src/compiler/10.frontend/core/lexer_scanners.spl` was "left
in place with a guard comment" — that file exists nowhere in the tree.
Low severity: correct the doc, no code action.

### 6. `interface_digest_of` — designed, wired to nothing (CONFIRMED, unchanged)

`/usr/bin/grep -rn interface_digest_of src --include=*.spl` → **3 hits, ZERO callers**:
- `src/compiler/80.driver/cache/action_key.spl:199` — the definition itself
- `src/compiler/35.semantics/interface/compile_interface.spl:37` — a **comment**
- `src/compiler/80.driver/cache/block/block_key.spl:10` — a **comment**

Never computed, not merely ignored. The caches that DO run are content-keyed
(`object_cache_key` hashes only the module's own source). Status matches
`.claude/rules/commands.md`; no drift.

### 7. `src/lib/simple.sdn` `dependencies:` — declared, never traversed (CONFIRMED)

`dependencies:` is declared at `src/lib/simple.sdn:14`. Grepping
`src/app/info/main.spl` and `src/compiler/80.driver/project.spl` for `dependencies`
returns **nothing** — neither the documented display reader nor the driver
traverses the key. Real target edges exist on paper; no build path consumes them.
This is why there is no partial build. Status matches the rules doc.

### 8. `src/lib/common/crypto/sha256_core.spl` — RETRACTED (false positive), one real defect found and fixed

**The "structurally un-importable" finding was wrong, and the visibility premise
behind it is wrong repo-wide.** In Simple a bare `fn` **is** module-exported;
`pub` is not required for cross-module import. Evidence:

- `src/lib/common/crypto/sha256.spl:5` already does
  `use std.common.crypto.sha256_core.{sha256_initial_hash, sha256_pad_message,
  sha256_process_block}`, and `sha256_simd.spl:11` imports from it too. The core
  was **already routed** — the "wiring step" this entry proposed was a no-op.
- `sha256.spl` itself has **0 `pub fn` / 9 bare `fn`**, yet ~20 compiler modules
  import it (`stable_id`, `compile_interface`, `module_identity`, `cas_store`,
  `action_key`, `block_key`, …) and the compiler builds. Under the retracted
  premise every one of those imports would be impossible.
- Repo-wide the ratio is 4,353 `pub fn` to 38,459 bare `fn` in `src/lib`; 24 of
  26 files in `common/crypto/` have zero `pub fn`. Bare `fn` is the norm, not a
  defect marker.
- Executed proof: importing `sha256_initial_hash` / `sha256_pad_message` /
  `sha256_process_block` across the module boundary runs and returns correct
  values. No visibility change and **no bootstrap** was needed.

Methodology note: `grep -c '^pub fn'` is **not** an importability oracle in this
language. Counting it as one is what produced this entry.

**The real defect this file did have** — surfaced by *running* it, not grepping
it — was a cross-module symbol collision the compiler reports as
`[compiler_cross_module_private_symbol_collision]`:

> `compress_block` has 2 co-compiled definitions with 2 differing signatures
> (`(i64,…,i64)->Tuple([i64,i64])` vs `(list,list)->list`); … a fallback hit may
> still dispatch to the wrong one.

`sha256_core.spl:85 compress_block(h, block)` collided with
`sha256.spl:406 compress_block(a,…,w)`. The core-side function is a
pattern-matchable wrapper with zero callers, and the MIR rule in
`mir_opt/pattern/rules_crypto.spl:43` targets the *`sha256.spl`* symbol, so the
core one was never the pattern target either. Fixed by renaming it
`sha256_core_compress_block`, matching its already-uniquely-named siblings
`sha256_core_msg_schedule1`/`2` — evidently the original author's intent, applied
to two of three wrappers. The warning is gone and digests are unchanged.

**How much of `sha256.spl` actually reaches the core — measured, not assumed.**
The `use` on line 5 is real but narrow, and the first version of this retraction
overstated it. Sabotage (IV `0x6a09e667`→`0x6a09e668`) is what settled it:

- `sha256_text()` / `sha256_bytes()` were **unaffected**. `sha256_text`
  (sha256.spl:197) hashes via the native runtime `rt_tls13_sha256`, so it never
  touches the pure-Simple core at all.
- Only `sha256_bytes_scalar()` (sha256.spl:381-392) calls
  `sha256_pad_message` / `sha256_initial_hash` / `sha256_process_block`.

So the core is genuinely live, but on exactly one path. That path was **already**
spec-covered too — `sha256_simd_parity_spec.spl:60` asserts the `"abc"` vector
against `sha256_bytes_scalar` and lines 64-85 assert SIMD/scalar parity — so the
entry's "No spec" claim was also wrong, though coverage was thin (one vector).

Standing oracle added: `test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl`
(mirrored to `test/unit/...`), 13 examples — three direct `sha256_core` primitive
checks, the five FIPS 180-4 vectors through `sha256_text`, and the same five
re-asserted through the core-routed `sha256_bytes_scalar`. All five digests were
cross-checked against `sha256sum` before use. The `sha256_bytes_scalar` block is
the one that gates the core: it goes red under the IV sabotage above, while the
`sha256_text` block does not — which is precisely why both are present, and why a
`sha256_text`-only spec would have been a vacuous guard on this file.

---

## Lower-confidence zero-importer candidates (recorded, NOT actioned)

Zero external references at audit time. **`use` is warn-only, so this is
fail-open** — none of these may be deleted on this signal alone. Sabotage with an
inverse control is required before any disposition.

| file | re-exported? | spec? |
|---|---|---|
| `src/compiler/70.backend/backend/native/operand_utils.spl` | yes (`__init__.spl`) | no |
| `src/compiler/70.backend/backend/common/verification_codegen.spl` | yes (`__init__.spl`) | no |
| `src/os/crypto/scram_common.spl` | no | no |
| `src/os/compositor/shared_mdi_host_seed.spl` | no | no |
| `src/lib/gc_async_mut/gpu/browser_engine/net/ws_utils.spl` | no | no |
| `src/lib/nogc_async_mut_noalloc/baremetal/common/string_extract.spl` | yes (mod+`__init__`) | no |
| `src/lib/common/js/engine/{parser_expressions,parser_statements,vm_builtins}.spl` | no | no |
| `src/lib/common/js/builtins/typed_array.spl` | no | no |
| `src/lib/common/crypto/{rsa_pkcs1,sha256_core}.spl` | no | no |
| `src/lib/common/compress/zstd_dict.spl` | no | no |
| `src/lib/common/wine_nt_api_*.spl` (4 files) | no | no |
| `src/lib/common/probe_residue_9977.spl` | no | no |
| `src/i18n/strings_common.ko.spl` | yes (`__init__.spl`) | no |
| under symlinked `src/compiler_rust/`: `tooling/{parse_utils,retry_utils,url_utils}.spl`, `tooling/compiler/types_util.spl`, `host/common/io/{progress_style,styled_string}.spl` | some | no |

**The JS-engine cluster is the highest-suspicion group**: `parser_expressions`,
`parser_statements`, `vm_builtins` are exactly the shape of a split-out that never
got its consumer. But interpreter eval files were proven last night to stay live
via **sibling preloading with zero `use` anywhere** — this cluster is the same
shape, so treat zero-importer here as unproven, not as dead.

---

## Positive controls (proving the method distinguishes)

- `doc/08_tracking/bug/cross_app_glyph_rasterization_diverges_2026-07-02.md` —
  "fixed, shared 5x7 table". `src/lib/common/ui/glyph_bitmap_5x7.spl` **exists**;
  `glyph_row_bits` / `glyph_index_for_char_code` / `FONT_ROWS_PACKED` have **17
  referencing files**, spanning both claimed consumer lanes plus
  `src/os/compositor/*`, `examples/06_io/ui/widget_showcase_gui.spl`, and the
  asserted gate `test/03_system/check/cross_app_glyph_consistency_spec.spl`.
  **Genuinely wired.**
- `doc/08_tracking/bug/three_layoutbox_variants_2026-08-10.md` — honestly
  self-labelled "PARTIALLY RESOLVED"; `src/lib/common/layout/box_model.spl` has
  real consumers (`src/app/ui.browser/{backend,event_bridge}.spl`). Not a
  false-resolve.

## Why nothing was wired this session

Every candidate failed at least one safety precondition, and the instruction was
to wire only what is safe **and covered by tests**:

- **arch/common (1)** — verification needs a SimpleOS kernel build; explicitly
  off-limits this session.
- **MCP framing (2)** — the two would-be dedupers have **no specs**; wiring an
  untested orphan is unverifiable. The tested route (mcpgdb → `lsp_transport`
  shim) touches live tool servers on a tree with six contending sessions.
- **CSS (3)** — blocked on a real type mismatch (`Color?` vs `u32`); needs an
  adapter, which is new design, not wiring.
- **sha256_core (8)** — needs a visibility change plus a bootstrap.

Recording precisely, per the rule: never delete on a fail-open signal, never
weaken a spec to green, never over-engineer.

## Actions required

1. **Correct paths only** in `rv32_rv64_rtl_unification_results_2026-07-21.md` —
   `riscv_rtl/common/` → `riscv_common/`. Status COMPLETE is CORRECT; do not
   reopen.
2. **Reopen** `browser_color_commonization_blocked_2026-05-10.md` — Resolved is
   false; record the `Color?`-vs-`u32` type mismatch as the actual blocker. This
   is the audit's **only** genuine false-Resolved.
3. **Correct** `lexer_position_unification_2026-07-29.md` disposition table (doc
   only).
4. Add a spec for `mcp_common.spl` / `mcp_startup_lib.shs`, then wire or delete.
5. Add specs for the three still-orphaned `arch/common` helpers so the next
   orphaning fails loudly.

## Systemic fix (the actual cure)

Every instance here is invisible for the same reason: **an extraction with no spec
cannot fail when it is orphaned.** Proposal: a lint/gate that flags a module under
a `common/`, `shared/`, or `util/` path which has zero importers **and** zero spec
references — reported as a warning with an explicit allowlist, so a deliberate
staged extraction is declared rather than silent. This must be a *reporting* gate,
not a deletion tool: `use` is warn-only and sibling preloading defeats importer
counting, so the signal is fail-open by construction and can only ever prompt a
human check.

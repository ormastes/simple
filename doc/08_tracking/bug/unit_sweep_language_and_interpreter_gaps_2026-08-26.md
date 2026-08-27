# Language / interpreter gaps surfaced by the full `test/01_unit` sweep (2026-08-26)

Found by the 5-agent sweep-fix campaign (`.spipe/simply_showcase/state.md`).
These are NOT spec/library typos — each needs a compiler or runtime change.
Mechanical failures were fixed and landed (`dddd834f996`, `c433e5d091d`,
`6e7b2eb616a`, `9c5595b146d`, `4907ce1da97`, `e5a10e3ee78`, `f65ae4a5f9c`,
`d9ca9d78b1d`, `2f3f215003b`).

## Grammar / parser

1. **Inline `if c: a else: b` expression** — "expected expression, found Else".
   Blocks `src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl:148` (5
   specs) and the multi-line `if … else if … else:` expressions in
   `src/lib/hardware/rv64gc_rtl/imac_protected_core.spl:296,529` (2 specs).
2. **`_1` placeholder inside a call argument** lifts the whole enclosing
   `expect(...)` argument into a lambda (worked around in
   `test/01_unit/std/common/text_helpers_spec.spl`).
3. **Typed empty-array constructor `[(i64,i64,i64,i64)]()`** fails at runtime
   with "variable `i64` not found" (worked around in `skia/resample_spec`).
4. **Unterminated f-string** on a 30-line embedded shell string
   (`hardware/debug/testbench_self_referential_generic_class_spec.spl`).

## Interpreter (Rust seed)

5. **Block-scoped `val` leaks out of the declaring `if` block only sometimes** —
   `idx3` declared in one `if` and read in the next: "variable not found".
   Fixed at call sites in `jwt/encode.spl`, `os/crypto/jwt.spl`; the same
   shape still fails in `browser_renderer_protocol_spec` and
   `wasm_host_spec` (match-arm binding `module_id`).
6. **`BTreeMap.new()` / `HashMap.new()` intercepted as builtin Dict before
   user-class lookup** (`interpreter_call/mod.rs:684`,
   `interpreter_method/mod.rs:1824`) — breaks both `src_collections_facade`
   specs; unfixable from `.spl`.
7. **`type X = SharedX` drops static constructors** (`X.new_persistent()` →
   nil); worked around with `export use …{SharedX as X}` in
   `db/dbfs_engine/{intent_log,checkpoint_ring}.spl`. Same class: a constructor
   annotated `-> Ref?` makes later `r.set()` mutations lost
   (`nogc_async_immut/ref/__init__.spl:150`).
8. **"cannot index assign value of type array"** — `sha512_verify`,
   `font_asset_manifest`, `simple_web_file_renderer`, `xz_lzma2`.
9. **Cross-module class-name collision** (`Rect` no field `x` when two modules
   define `Rect`) — `wine_x11_adapter`, `wine_gui_hello`.
10. **Flattened-unit name collision self-recurses** (`file_rename` stack
    overflow) — both `dbfs_meta_store_facade` specs.
11. **`Any?` return of an enum payload arrives as the enum** — `option_ce`.
12. Legacy `import string` resolves to the `bm_*` dict — both
    `oauth_*_random_int_repro` specs.

## Missing runtime backing (SFFI)

`rt_thread_sleep_ms`, `rt_signal_install`, `rt_check_file_path`,
`rt_ensure_dir`, `rt_font_glyph_index`, `rt_font_load`, `rt_dma_alloc`,
`rt_counterpart_open`; `rt_thread_id` arity mismatch (expects 1 arg).

## Not bugs — spec drift needing a rewrite

`browser_engine/*` DOM model (`.tag/.classes` vs `tag_name/attributes`,
`execute_with_type`), `layout_*` (`layout_inline(doc, ctx)` never existed),
`gc_async_mut/**_facade_spec` (facades never existed; real specs live under
`nogc_async_mut/`), engine 3D/ids API drift, `text/*` Phase-5 modules,
`JsonValue` removal, hardware VHDL/SV content oracles.

## Wave 3 additions (`676241b1db3`, `9db7dbb836d`)

13. `skia/entity/canvas.spl`: `if val rec = self.recorder: rec.record(...)`
    mutates a COW copy — canvas recording never captures ops (`op_count` 0).
14. Seed mock SQL engine (`interpreter_extern/sffi_db.rs`) rejects column-less
    `INSERT INTO t VALUES (...)` and bound params — 6 `database/sql/*` specs.
15. Text slicing `value[1..n-1]` is byte-based in the seed while
    `strip_quotes` assumes char semantics (`sdn_reader_utf8`, em-dash).
16. CUDA reported unavailable (`env_skip`) on a host with two working NVIDIA
    GPUs — detection gap in the cuda specs' env probe.
17. ROCm/HIP out-pointer results were read from the DynLib return status
    (fixed in `ffi_rocm`/`sffi_rocm`); missing externs `rt_font_load`,
    `rt_engine2d_pack_args_4`.

## Wave 4 additions (compiler tree; `97c30fce71e` `c8f1bf0c2c2` `bfe408434dd` `179e18fc740` `45b92648ff8` `4345c8e197b` `8e9ef608092`)

18. **Stale-snapshot clobber `4edef8fab8e`** ("snapshot current development
    state", 624 files, -45k lines) deleted still-imported code:
    `Sha256StreamV1`, `warning_phase.spl`, `driver_safety_severity.spl`,
    ModuleSurface `semantic_hash`, driver entry-scan-cache API, lint-engine
    internals. 7+2 files restored; ~600 files unaudited — see
    `doc/08_tracking/bug/stale_snapshot_clobber_4edef8fab8e_2026-08-26.md`.
    Lint-engine restore is entangled (fixes raw_rt_access, regresses
    riscv_rtl `sort_by`) — documented, not landed.
19. Interpolation holes inside `to_contain("...{x}...")` literals silently
    interpolate — escape as `\{...\}` in source-contract specs.
20. Flattened method → free fn (`OptimizationPass.new` →
    `optimizationpass_new`) left stale call sites in
    `optimization_passes.spl` (fixed).
21. `std.bare.hal` resolves from a third stdlib root, so lib fixes there are
    unverifiable in-tree (`hal_traits`); `Option.some/none` vs `Some/None`
    mismatch fixed in `bare/hal/uart.spl` regardless.
22. Seed needs redeploy for the `feature` keyword (bdd_feature_group).

## Wave 5 additions (~34 specs fixed)

Landed shas — slice0 `7971f2bffbb` `6a02c0f8c4c` `745540b000e` `5c219ddf6d2`;
slice1 `a41ef500f83` `64f8098101d` `11c816c21d9` `06fa37dc08f` `284ce63b0ac`;
slice2 `dc58fec5f1b` `8da31723373`; slice3 `e5a7528f063` `46bb8524167`
`1f3c1225f8b` `aa0fbd39bdf`.

23. **Seed parser rejects multi-line `if` conditions** when a continuation line
    starts with `self` or `_`, or when the body indent equals the continuation
    indent. Workaround applied across the sweep was to hoist the condition into
    a local `val`; that is a workaround, not a fix — the grammar should accept
    the compact form. Needs a seed parser change.
    **FIXED 2026-08-27 — two defects, and the reported framing was misleading
    on both.**
    - *"expected Indent, found Self_/Underscore".* NOT an indentation defect.
      When an `if`/`while` condition uses a multi-line operator continuation at
      the SAME column as the body, the lexer emits no fresh `Indent` for the
      body, so `header_continuation_is_equal_column` (`parser_helpers.rs`) asks
      `is_statement_start()` whether the body's first token opens a statement.
      That list (`parser_impl/core.rs`) contained `Identifier` and `Me` but
      omitted `Self_` and `Underscore`, so a body beginning `self.x = …` fell
      through to `expect(Indent)`. Any other leading token — an ordinary
      identifier included — parsed fine, which is exactly why it read as an
      indentation problem. Fixed by completing the token list; both callers
      (the equal-column check and `parse_block_after_newline`'s flat-body
      shape) genuinely want "can a statement start here", and `self.x = 1` /
      `_ = f()` qualify, so this is not a grammar weakening. The "body indent
      equals the continuation indent" clause in the original report is a
      necessary condition, not the cause.
    - *"expected identifier, found Newline" in the hoisted-`val` case*
      (`authenticated_fs_exec_submission_service_v1.spl`, 3 sshd specs). The
      recorded suspicion of a `.?` or `==`/`!=` continuation is WRONG. It is the
      TYPE ANNOTATION that wraps: `var g_service_v1:` / newline /
      `AuthenticatedFsExecUserServiceV1? = nil`. The trailing-colon continuation
      now mirrors the trailing-`=` continuation `var_decl.rs` already accepted;
      the consumed Indent's compensating Dedent is drained after the
      initializer, since `= nil` sits on the continuation line. A colon whose
      next line is not an indented type is put back, so genuinely malformed
      input still produces the original diagnostic.
    Gates: `parser/src/multiline_condition_self_body_test.rs` (7 tests, incl.
    the previously-working shapes that hid the defect, and must-still-reject
    cases for a type annotation with no type) and
    `test/01_unit/language/multiline_condition_self_body_spec.spl` (5 green).
    Full parser suite 319 green. All five product files named across items
    23-25 now parse.
24. **Inline `unsafe(caps): expr` one-line body rejected.** Only the
    block/indented form parses; the one-line colon form is a documented shape
    that the seed does not accept.
    **FIXED 2026-08-27.** Cause: `parse_unsafe_block_primary`
    (`parser/src/expressions/primary/mod.rs`) called `parse_block`, which
    accepts only the indented form; the inline body then hit "expected Newline,
    found Identifier". Routed the body through the existing
    `parse_inline_or_block` helper, which handles both shapes and additionally
    reconciles a pseudo-DEDENT left by a preceding condition continuation.
    The 13-site block-form workaround in `src/os/kernel/boot/mmio_hardware.spl`
    was reverted in the same change; that file now parses. Regression gates:
    `parser/src/unsafe_inline_body_test.rs` (4 tests, incl. inline `unsafe`
    inside `if`/`while` bodies and after a multi-line condition continuation,
    plus must-still-reject cases for a missing colon and an unterminated
    header) and `test/01_unit/language/unsafe_inline_body_spec.spl` (4 green).
    Known pre-existing laxness left alone: `unsafe(caps):` with no body at all
    is accepted both before and after this change.
25. **"expected expression, found Dedent"** in three `src/os/port/*.spl` files.
    Undiagnosed — the error points at a dedent with no obvious offending
    construct; needs a reduced repro before it can be filed against a specific
    grammar rule.
    **DIAGNOSED AND FIXED 2026-08-27 — it was TWO unrelated defects, not one.**
    - *Grammar defect (2 of the 3 files:* `initramfs_validate.spl`,
      `guest_toolchain_artifact_build_receipt.spl`*).* Minimal repro:
      `val p = g() ??` newline `    return Err("m")`. `return` is usable as a
      plain identifier in primary position, so the `??` fallback parser
      (`parser/src/expressions/postfix.rs`, `DoubleQuestion` arm) read `return`
      as a NAME and its operand as a no-paren call argument; on the multi-line
      form that scan ran past the statement's Newline and died at the enclosing
      block's DEDENT. A BARE `return` (no operand) parsed fine, which is what
      hid it, and so did the same-line form. Fixed by building
      `Expr::UnwrapOrReturn` — `expr ?? return X` simply IS
      `expr unwrap or_return: X`, and that node already has diverging semantics
      wired through the interpreter and every backend. (Building
      `Expr::DoBlock([Return])` was tried first and is WRONG: a Coalesce default
      is lazily evaluated, so it arrives as a thunk — "cannot convert function
      to int".) Both shapes now share the same semantics.
      **Sub-item, still open:** `??` with a `break`/`continue` fallback. There is
      no loop-control counterpart to `UnwrapOrReturn`; it parses (as a bare
      identifier, exactly as before this change) but has no defined runtime
      behaviour. Deliberately out of scope, not regressed, not claimed fixed.
    - *Not a grammar defect at all (the 3rd file,*
      `qrb2210_adreno_vulkan_kernel_transport.spl`*).* Three `val cond_NNN =
      not f(...)` hoist workarounds were left with a literal unbalanced extra
      `)` (lines 207, 232, 257). Fixed as source. The trailing-comma theory
      recorded earlier was correctly disproven — it was never a comma.
    Gates: `parser/src/coalesce_diverging_fallback_test.rs` (4 tests, incl.
    must-still-reject cases for `??` before `)` and `,`) and
    `test/01_unit/language/coalesce_diverging_fallback_spec.spl` (4 green,
    asserting runtime DIVERGENCE, not just parse acceptance). All three files
    now parse.
26. **Free functions of the form `fn treesitter_*(self: TreeSitter)` do not
    resolve as methods across module boundaries.** Method-call syntax on an
    imported type only finds the flattened free fn when it is declared in the
    same module, so cross-module call sites fail to resolve.
27. **HIR→MIR lowering returns nil internals** for multi-function sources that
    use `and`/`or`. Single-function sources lower correctly; the defect appears
    only once more than one function is present, pointing at per-function state
    reuse in the lowering pass.
28. **Clobber `4edef8fab8e` also truncated 7 spec files to 1 byte.** Five have
    been restored; two remain wiped and are recoverable from `26de1a115c3`.
    This widens item 18 above: the clobber damaged tests as well as source.
29. **MCP core tool set collapsed to 3 tools (expected 20).** In addition, the
    `perf` command appears in both the help text and the dispatch table but has
    no dispatch branch, so invoking it falls through silently.
30. **`test_db.sdn` lock contention under concurrent lanes.** Parallel test
    lanes contend on the shared results DB; sweeps running alongside other
    sessions can stall or lose rows. Sweep verdicts should not depend on a
    single shared writable DB file.

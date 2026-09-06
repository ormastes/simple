# enum_impl_static_fn_scoping — scoping the enum-associated-fn defect (no fix landed)

Lane: ENUMSCOPE (2026-07-29). **Scoping/measurement only — no `src/**` file was
modified.** Report:
`doc/08_tracking/bug/enum_impl_static_fn_scoping_2026-07-29.md`.

Parent bugs: `enum_associated_fn_never_called_on_jit_2026-07-28.md`,
`enum_assoc_fn_residual_exposure_2026-07-28.md`. Prior fix: `362b206e7e4`
(rejects undeclared `EnumName.member`, does not touch the declared case).

**Binary under test:** `src/compiler_rust/target/debug/simple`, built by this
lane (`cargo build -p simple-driver --bin simple`), mtime 2026-07-29 01:05:36
UTC. `src/compiler_rust/` had one unrelated concurrent edit
(`runtime/src/value/sffi/io_print.rs`) from another session at build time;
did not touch the MIR/HIR/interpreter files this lane investigated.

## Result

| | |
|---|---|
| Forms characterized | 4: impl-block static (same file), enum-body static, enum-body plain method, impl-block static (cross-module) |
| JIT-broken forms | 3 of 4 — impl-block-same-file, enum-body-static, impl-block-cross-module (all fabricate identically) |
| JIT-correct forms | 1 of 4 — enum-body plain method via instance dispatch (different lowering path entirely) |
| Interpreter-broken forms | 1 of 4 — impl-block static, **same file as call site** (false rejection) |
| Interpreter-correct forms | 3 of 4 — enum-body static, enum-body plain method, impl-block cross-module |
| 151-site claim (config.spl) | **NOT reproduced** — real count is 6 (matches prior doc), 12 total dotted calls in file, 53 repo-wide references to its 2 enums |
| Fix landed | **none** — see report §5/§6 for why not |

## Key findings

1. **The JIT defect is uniform across impl-block vs enum-body vs
   same-file-vs-cross-module** — all three broken forms fabricate identically,
   because HIR registration (`module_pass.rs:398-407` vs `:412-425`) treats
   them byte-for-byte the same. There is no smaller fix that special-cases
   "impl block only."
2. **A second, previously undocumented interpreter bug**: same-file
   `impl Enum:` statics are falsely rejected by the interpreter, while
   enum-body statics AND cross-module impl-block statics in the same
   interpreter are correct. This reconciles the apparent contradiction
   between the two parent docs (one showed interp correct, the task's
   motivating example showed interp rejecting) — they were measuring
   different forms, not disagreeing.
3. **The "151 sites" / "extending the guard" framing is likely a
   mischaracterization of the fix, not just an unverified number.** The
   guard (`lowering_expr_call.rs:445-454`) already exempts
   `global_types`-registered names (which is exactly where impl-declared AND
   enum-body-declared statics live) — extending its rejection scope wouldn't
   change behavior for those names at all. The actual bug is that the
   **fabrication branches right after the guard** (lines 456, 572) don't
   consult `global_types`/`available_functions` the way the guard does, so
   they fabricate regardless. The real minimal JIT fix reuses the guard's
   existing condition to gate fabrication, not to reject more calls.
4. Found one more adjacent unguarded fabrication site not covered by
   `362b206e7e4` at all: `lowering_expr_ident.rs:36-50`, bare (non-call)
   `EnumName.field` references — same bug class, out of scope for this task's
   three call forms but worth a follow-up bug.

## Why not fixed here

Two independent defects (MIR lowering fabrication; interpreter entry-script
impl registration gap, not yet bisected past "somewhere upstream of
`interpreter_eval.rs` Node::Impl handling, specific to
`driver/src/interpreter.rs:100 run()`'s direct-script path vs the
import-loader path"). The JIT half is small and well-understood in isolation
(~4-6 line diff); the interpreter half's size is unknown until bisected
further. Landing only the JIT half would newly flip form (a) into
cross-engine disagreement (JIT correct, interpreter still wrong) rather than
resolve it, and the task's verification bar (full rebuild + both-engine
verification + regression sweep vs a true baseline) is multi-hour work not
attempted in this scoping lane.

## Next step (for whoever picks this up)

1. Land the JIT fix (report §5, step 1) and re-check
   `enum_assoc_fn_residual_exposure_2026-07-28.md`'s probes #1-#3.
2. Bisect the interpreter gap using probes (a) vs (d) as the differential.
3. Full bootstrap + regression sweep covering both together.

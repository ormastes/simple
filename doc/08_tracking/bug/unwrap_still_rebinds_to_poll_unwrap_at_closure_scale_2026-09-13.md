# `.unwrap()` still rebinds to `Poll.unwrap` at closure scale via a second route (2026-09-13)

Status: OPEN. Residual of
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` (PR #750), which
is RESOLVED for the site it names and NOT for the whole population.

## Measurement — this is the honest number

PR #750 guarded `mangle_mir`'s two bare `.method` scans. Counting `bl` edges to
`_lib__nogc_async_mut__async__poll__Poll.unwrap` in the Stage 2 candidate,
before and after, on this host:

| | call sites | distinct calling functions |
|---|---|---|
| run 15 candidate (before) | 270 | 144 (incl. `Poll.unwrap`'s own frame) |
| run 17 candidate (after) | **208** | **109** |

So PR #750 cleared 62 sites — including the one that mattered,
`find_linker_path`, which now correctly reads `bl <_rt_unwrap_or_trap>` — and
**208 remain**. Zero legitimate external `Poll.unwrap` callers exist in this
tree, so essentially all 208 are miscompiled the same way: a `.unwrap()` that
should lower to the builtin is calling an unrelated type's method, which returns
0 for a non-`Poll` receiver.

**Correcting the record:** PR #750's body and the predecessor's RESOLVED section
describe the 270-site blast radius in a way that reads as if the fix cleared all
of it. It cleared 62. That overstatement is corrected here and in those
documents.

## What is already ruled out — do not re-test these

With the PR #750 seed, in a 2-unit closure that DOES contain a competing user
method named `unwrap` (the ingredient without which nothing reproduces at all),
every one of these prints correctly:

```
val p = find_it(); if p.?: Ok(p.unwrap())      -- the original blocker shape
val a: text? = "/annotated"; a.unwrap()        -- explicitly annotated local
opt_call().unwrap()                            -- direct call receiver
res_call().unwrap()                            -- Result receiver
h.slot.unwrap()                                -- struct field receiver
opt_call().unwrap().trim()                     -- chained
rv.unwrap()                                    -- the genuine user method, still correct
```

So the residual route needs something a 2-unit closure does not have. The
reproducer harness is `repro/{rival,main}.spl` + `repro.sh` (2.6 s per
iteration); extend it rather than starting over.

## Leading hypothesis (NOT confirmed)

`resolve_call_target` (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`)
has its own qualified-name fallback with **no** enum-helper guard and no type
restriction:

```rust
let candidates = local_suffix_index.get(lookup_name)
    .or_else(|| suffix_index.get(lookup_name))
    .or_else(|| local_suffix_index.get(method))   // qualifier DISCARDED
    .or_else(|| suffix_index.get(method));
let best = candidates.iter().find(|c| c.to_lowercase().contains(&type_part.to_lowercase()))
    .or_else(|| if candidates.len() == 1 { candidates.first() } else { None });
```

A qualified `text.unwrap` skips the bare guard (it contains a dot), fails
`resolve_name_variants`, matches no candidate containing "text", and is then
returned by the single-candidate arm. The `resolve_by_suffix` fall-throughs
immediately below have the same shape. `codegen/llvm/functions/calls.rs`
(module-wide `.unwrap` scan, shortest name wins) is a second candidate, reachable
for an already-qualified name, since `bare_rt_redirect` fires only on exactly
`"unwrap"`.

This is a hypothesis because the 2-unit probes above did NOT produce a qualified
`text.unwrap` — the route that generates one has not been identified.

## Suggested next step

1. Pick one residual caller (list below) and disassemble it to see what feeds
   `x0` before the `bl` — the receiver shape is the thing to reproduce.
2. `resolve_call_target` is a standalone function like its twin, so it is
   unit-testable exactly the way
   `text_qualified_enum_helpers_never_rebind_to_a_lone_user_method` tests
   `resolve_method_call_static`. Write the test first.
3. Guard the single-candidate arm and the `resolve_by_suffix` fall-throughs with
   `is_enum_helper_method`; check whether `calls.rs` needs it too.
4. Verify by re-counting `bl …Poll.unwrap` on the next Stage 2 candidate — the
   number should fall to 0 external callers. **Count the instruction; do not
   infer from a passing verdict.**

Sample residual callers (109 total):

```
MirToLlvm.lookup_function_return_unsigned
MirToLlvm.translate_module_with_entry_policy
MirToLlvm.llvm_format_span
cranelift_codegen_adapter.compile_function
cranelift_codegen_adapter.cranelift_static_init_bits_value
cranelift_codegen_adapter.cranelift_static_init_supported
```

## Why this did not block Stage 2

Stage 2 builds and now reaches a real link failure (`-lc`, see
`stage2_sanity_darwin_link_passes_lc_2026-09-13.md`). These 208 sites are latent:
each returns 0 where a payload was expected, and only bites when the value is
used in a way that notices. `find_linker_path` noticed. The rest are unexploded.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` (predecessor)
- `doc/08_tracking/bug/stage2_sanity_darwin_link_passes_lc_2026-09-13.md` (current Stage 2 blocker)
- PR #750

## Runs 18 and 19 (2026-09-13) — four holes closed, the count did NOT move

**Headline, stated before the detail so it cannot be misread the way PR #750's
was: the residual is STILL OPEN.** Two full Stage 2 bootstraps were built and
measured. The count is **208 sites / 109 functions in run 17, run 18 and run
19 — byte-identical, unchanged.** Four genuine name-resolution holes were found
and closed along the way; none of them is the producer of these 208 sites.

### Measurement, and an instrument you can trust

`count_poll.sh` (recipe below) disassembles the candidate, tracks the current
function symbol, and counts `bl` edges to
`_lib__nogc_async_mut__async__poll__Poll.unwrap` excluding `Poll.unwrap`'s own
frame. Fail-closed: it ERRORs unless the symbol is defined AND the binary
carries >100 text symbols, >100 disassembly function headers and >100
symbol-annotated `bl` operands — a zero from an unsymbolized or missing binary
is never reported as a pass.

```sh
otool -tv "$BIN" | awk '
/^_[A-Za-z_].*:$/ { fn = substr($0, 1, length($0)-1); next }
/bl[ \t]+.*_lib__nogc_async_mut__async__poll__Poll\.unwrap/ {
    if (fn != "_lib__nogc_async_mut__async__poll__Poll.unwrap") { n++; fns[fn]=1 }
}
END { c=0; for (f in fns) c++; printf "external_sites=%d external_functions=%d\n", n, c }'
```

| candidate | external sites | functions |
|---|---|---|
| three pre-PR-#750 sibling candidates (baseline) | 265 | 142 |
| run 18 (mangler guards, routes 1-3) | **208** | **109** |
| run 19 (+ LLVM MethodCallStatic guard, route 4) | **208** | **109** |

The doc above reports 270/144 and 208/109 by a different instrument; 265 vs 270
is instrument skew on the same artifact class, not a change. **Both of my
numbers come from the same script, so the before/after is internally valid — and
it shows no movement.**

**A vacuous-zero trap, recorded because it nearly became a false victory.** The
first count on run 18 returned `external_sites=0` with healthy non-vacuity
numbers. It was wrong: the sanity step renamed the candidate from `simple` to
`simple.rejected` *between* the script's `grep` passes and its `awk` pass, so the
final `otool` read a path that no longer existed and produced no output. The
non-vacuity gates ran on the earlier passes and could not see it. **Copy the
candidate aside before measuring it**, and re-run any zero before believing it.

### The four holes that WERE closed (real, unit-proven, not the producer)

Each is a genuine defect — a qualified `<Type>.unwrap` reaching a resolver that
discards the qualifier — with a discriminating test. They are worth having; they
are simply not what emits these 208 `bl`s.

1. `mangle.rs:774` `resolve_call_target` — the doc's leading hypothesis.
   `.get(method)` drops the qualifier and the `candidates.len() == 1` arm plus
   both `resolve_by_suffix` fall-throughs fire regardless of receiver type.
2. `mangle.rs:1013` `resolve_method_call_static`'s generic owner filter —
   `find(|c| c.to_lowercase().contains(&type_part_lower))` is a substring test
   against the FULL mangled path, so `T.unwrap`, `Mut.unwrap`, `Async.unwrap`,
   `Lib.unwrap`, `As.unwrap`, `Wrap.unwrap` all match
   `lib__nogc_async_mut__async__poll__poll.unwrap` by accident. PR #750's
   str/text/string arm is one narrow special case of this same hole.
3. `codegen/instr/closures_structs.rs:1151` (Cranelift twin) — `enum_helper` was
   keyed on the WHOLE `lookup_name`, so a qualified helper was not recognised as
   one and every scan below ran, including the bare `use_map.get(method)`.
4. `codegen/llvm/functions.rs:2828` — `qualified_owner_is_user_type` classifies
   `i64.unwrap` as a user-type method, so `runtime_func` becomes `None` and the
   fall-back's module-wide `.unwrap` suffix scan takes its single match
   unconditionally (its arity/owner narrowing only runs when `matches.len() > 1`).

Fix shape, shared: `enum_helper_owner_matches` (`mangle.rs:207`) accepts a rebind
only on an exact owner-segment match; the Cranelift predicate is re-keyed on the
method segment; the LLVM classifier treats a payload-type qualifier (no `__` in
the owner) as not-a-user-type. A genuine `Poll.unwrap` still resolves.

**Checked, not assumed:** leaving a qualified name unresolved is safe.
`codegen/llvm/functions/calls.rs` has a `qualified_rt_redirect` table inside
`if let Some(dot_pos) = qualified_name.rfind('.')` with no type restriction,
covering all seven helpers, so an unresolved `MirStaticInit.unwrap` lowers to
`rt_unwrap_or_trap` and cannot become an undefined symbol.

### What the next session should do INSTEAD of guarding another resolver

Four resolver guards in a row moved the number by zero. Stop guarding resolvers.

1. **Test the null hypothesis first: are these 208 sites a MISCOMPILE at all?**
   Nobody has verified that. `Poll.unwrap` may be the canonical symbol the
   backend emits for a shared/monomorphized enum `unwrap`, in which case the
   name is cosmetic, the 208 are correct, and `find_linker_path` was a
   *different* defect that PR #750 happened to fix. Disassemble one survivor
   (`_compiler__common___Attributes__layout_attrs__parse_platform_attrs`, whose
   source shape is a plain `val x = f(); if x.?: x.unwrap()` on an `i64?`), read
   what feeds `x0`, and step into `Poll.unwrap` to see whether its body is a
   generic payload reader or genuinely Poll-specific. **If it is generic, this
   whole chain is chasing a naming artifact and the record should say so.**
2. Only if it IS a miscompile: instrument the EMITTER, not the resolvers. Add a
   default-off trace at the point a `bl` to `Poll.unwrap` is emitted, printing
   the MIR instruction kind and the pre-resolution name. Four sessions of
   reading resolution code have produced four correct fixes and zero movement;
   one trace would name the producer directly.
3. The survivor list is stable and includes `MirLowering.lower_lambda_value`,
   `CraneliftCodegenState.compile_inst`, `InterpreterBackendImpl.eval_expr` —
   lambda/closure and indirect-dispatch paths are over-represented, which is
   consistent with `MirInst::CallIndirect` or a closure-capture path (both named
   as candidates in the original task and both still unexamined).

### Stage 2 verdict, verbatim (runs 18 and 19, identical)

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: in-process native-build: LLVM native linking failed: Linking failed: cc linking failed: ld: library 'System' not found
clang: error: linker command failed with exit code 1 (use -v to see invocation)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

This is a NEW blocker and it is not in this lane: run 18/19 are rebased onto
PR #752 (`05e6c1f0041`, "key the native link line on the target, not on a Linux
shape"), which replaced `ld: library 'c' not found` with `ld: library 'System'
not found`. macOS needs no explicit `-lSystem` at all (clang links libSystem by
default) and the SDK path is not being passed, so the successor defect belongs
to `src/compiler/70.backend/linker/**`. Stage 3 was therefore never reached.

Rejected Stage 2 candidate (run 19), preserved, not deployed:
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
139328328 bytes. Run 18's: 139328456 bytes, sha256
`e4346afc60c640973007e906e75cb9e429893d29dab5b1063ab69e1c91691f68`.

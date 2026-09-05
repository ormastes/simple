# Lane CAUDIT — compound-assignment audit

Date: 2026-07-27. Binary used: `build/native_probe/simple` (see caveat below).

## Headline: the briefed premise was wrong on two counts

The lane was briefed as "`obj.field += v` is silently wrong on the JIT; the load
side yields 0 so it computes `0 <op> rhs`; plain locals (`i += 1`) are FINE".
Probing shows both halves of that are incorrect.

1. **The miscompile is `target = rhs`, not `0 <op> rhs`.** The load *and* the
   operator are dropped; the RHS is simply stored. `y = 100; y -= 7` yields `7`,
   not `-7` and not `93`. The briefed "0 + 2 = 2" reading was a coincidence of
   the `+=`/`n=5`/`rhs=2` example.
2. **Plain local variables are equally broken.** `var x = 100; x += 7` → `7`.
   `var sum = 0; for k in 0..5: sum += k` → `4` (the last `k`), not `10`.
   The instruction "locals are fine, do not touch" does not hold on this binary.

The explicit form (`x.f = x.f + v`, `z = z + 7`) is correct in every case tested,
on both engines. The interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) is correct
for locals and struct fields, and *rejects* index compound assign outright
("unsupported augmented assignment target").

Evidence: `build/caudit_probe/EVIDENCE.txt`, probes `probe{,2,3}.spl`.

### Caveat that bounds all of the above
Both `bin/simple` and `build/native_probe/simple` print
*"this Rust-built Simple binary is a bootstrap seed only; do not use it as the
normal tool"*. `bin/simple` is currently seed-clobbered (symlink →
`bin/release/x86_64-unknown-linux-gnu/simple`), and no genuine self-hosted
binary is available (redeploy-blocked). So this is measured on the **seed**, and
I could not confirm whether the production self-hosted compiler shares the
defect. Circumstantial argument that it does *not*: 343 in-scope local `+=`
sites exist (the compiler itself uses them), and a universal compound-assign
failure would make the repo non-functional. Someone with a real self-hosted
binary must re-run `build/caudit_probe/probe3.spl` before this is triaged.

## Audit table

Counting method: all `+= -= *= /= %=` (the complete operator set, per
`src/compiler/10.frontend/lexer_types.spl:109-113`) in owned `src/**` `.spl`/`.shs`,
excluding vendored paths and the other lanes' reserved paths.

| Stage | Count |
|---|---|
| Total compound-assign text hits, owned src | 741 |
| In scope after lane exclusions | 367 |
| Target-shape = struct field or index | 24 |
| — false positive (docstring / comment / string literal) | 20 |
| — real struct-field targets | 4 |
| — of which in **live** code | **0** |
| Target-shape = plain local (left alone per brief) | 343 |

### The 24 field/index-shaped hits

| file:line | target shape | verdict | action |
|---|---|---|---|
| `src/compiler/10.frontend/parser_extensions.spl:224` | `self.count += 1` | **false positive — inside a `"""` docstring** (`Example:` block of `parse_actor_body`) | none |
| `src/compiler/35.semantics/lint/_SimdOpportunityLint/byte_checks.spl:223,234,254` | `histogram[a[i]] += 1` | false positive — `#` comments | none |
| `src/compiler/35.semantics/lint/_SimdOpportunityLint/byte_checks.spl:256` | `"[a[{lvar}]] += 1"` | false positive — string literal (lint pattern matcher) | none |
| `src/compiler/90.tools/sffi_gen/types.spl:227` | `"fctx.next_value_id += 1;\n"` | false positive — string literal emitting Rust | none |
| `src/compiler/90.tools/sffi_gen/specs/cranelift_codegen.spl:231,291` | same | false positive — string literal | none |
| `src/app/ffi_gen.specs/cranelift_core.spl:454,514` | same | false positive — string literal | none |
| `src/app/compile/native_profile_counter.spl:335,518,528,532` | `"...[N] += 1u;"` | false positive — string literal emitting C | none |
| `src/os/crypto/curve448.spl:194,196,197,198` | `h[i] += t[k]` | false positive — comments (algorithm notes) | none |
| `src/os/crypto/tiger.spl:141` | `state[2] += c` | false positive — comment | none |
| `src/os/ml/kernels.spl:63` | `sdata[tid] += ...` | false positive — PTX source string literal | none |
| `src/app/interpreter/helpers/debug.spl:195` | `bp.hit_count += 1` | **real** (dead code) | **converted** |
| `src/app/interpreter/helpers/macros.spl:73` | `expander.expansion_depth += 1` | **real** (dead code) | **converted** |
| `src/app/interpreter/helpers/macros.spl:80` | `expander.expansion_depth -= 1` | **real** (dead code) | **converted** |
| `src/app/interpreter/helpers/macros.spl:85` | `expander.expansion_depth -= 1` | **real** (dead code) | **converted** |

## Sites converted (4)

All four are in `src/app/interpreter/`, which is **removed/dead code**:
- `src/app/__init__.spl:33` — "`app.interpreter` - REMOVED. Use `core.interpreter` instead".
- `src/compiler/10.frontend/core/interpreter/mod.spl:21` — "Location: `src/app/interpreter/` (removed)".
- No live `use` outside the subtree imports it; the only importers are its own files.
- The files are written in a Rust-transliterated pseudo-syntax (`&str`, `u32`,
  `&mut`, `Result<>`, `.to_string()`), and the sibling `debug_spec.spl` uses
  Python-style `from ..core import {...}` and does not parse at all.

Conversions (each provably equivalent; receiver is a simple local binding in
every case, so there is no double evaluation of a side-effecting expression):
- `bp.hit_count += 1` → `bp.hit_count = bp.hit_count + 1`
- `expander.expansion_depth += 1` → `... = expander.expansion_depth + 1`
- `expander.expansion_depth -= 1` → `... = expander.expansion_depth - 1` (×2)

**These conversions do not remove any live exposure**, because the code is dead.
They are worth keeping only so the hazard is absent if the module is ever revived.

## Verification

- `simple lint` on both touched files: **0 errors**, 12 warnings (unchanged from HEAD).
- **No runnable spec covers either file.** `src/app/interpreter/helpers/debug_spec.spl`
  fails to parse — verified byte-identical to `HEAD` (`diff -q`), so the failure is
  pre-existing and unrelated to this change. `macros.spl` has no spec at all.
  I am not claiming spec coverage for these edits.
- My total diff is exactly the 4 one-line changes above (`git diff` verified).

## Left alone deliberately

- **343 in-scope local-variable compound assigns.** The brief said not to touch
  them. Given finding (2) they are *equally* miscompiled on the seed JIT, so this
  exclusion should be revisited — but converting 343 sites is a different, much
  larger decision than this lane was scoped for, and it is the wrong remedy
  anyway (see below).
- All lane-reserved paths: `src/compiler_rust/**`, `src/compiler/50.mir/**`,
  `src/compiler/70.backend/**`, `src/compiler/10.frontend/core/interpreter/**`,
  `src/lib/common/ui/builder.spl`, `src/os/services/llm/**`,
  `src/os/services/pm_service.spl`, `src/lib/*/ecs/**`.

## Recommendation

Source-level conversion is the wrong remedy at this scale. With locals affected,
"remove the exposure by rewriting call sites" would mean touching every one of
the 367 in-scope sites (741 repo-wide) and permanently giving up a language
feature. The defect must be fixed in the compiler (lane JITCA). The useful
outputs of this lane are the corrected characterisation and the reproducer, not
the 4 dead-code edits.

Priority action: get a genuine self-hosted binary and re-run
`build/caudit_probe/probe3.spl`. If the production compiler reproduces this,
it is a release blocker far larger than a struct-field issue.

# private-symbol collision: sshd's four names — enumeration + mis-dispatch verdict

- **ID:** private_symbol_collision_sshd_four_names_2026-07-28
- **Date:** 2026-07-28
- **Status:** PARTIALLY FIXED 2026-08-09 (source-side renames landed; compiler-side
  C1/C2 still OPEN — compiler trees have live lanes). Re-verified: `_u8_at`,
  `_cswap_pair`, and `_ladder_step` are **no longer present** in
  `curve25519_smalllimb.spl` at all (superseded by unrelated refactoring —
  `_u8_at_i`, `fe_cswap`; no separate `_ladder_step` helper remains), so those
  3 of 4 collision groups are already gone. The 4th (`_hex_digit`, 11
  definitions) still had the encoder/decoder split from "Proposed remedy"
  below applied in this pass: the three `(text)->i64` decoders
  (`embedded_certs.spl`, `protocol.spl`, `wm_quality_contract.spl`) renamed to
  `_hex_digit_from_char`, and the odd `(u8)->u8` variant
  (`dual_backend.spl:89`, dead code — no in-file callers) renamed to
  `_hex_digit_byte`. Verified via targeted `bin/simple compile --emit-mir` on
  each touched file: no `_hex_digit`-related
  `compiler_cross_module_private_symbol_collision` warning remains (other,
  unrelated collision warnings like `_css_var`/`compress_block`/`shell` in
  `wm_quality_contract.spl` are pre-existing and out of scope). The remaining
  7 `_hex_digit(i64|i32)->text` encoder definitions still share a name and
  will still warn if wildcard-imported together, but per the verdict below
  they agree on every in-range input, so this residual collision is the
  documented **benign** class, not the encoder/decoder cross-direction hazard
  this pass closed. C1 (include return type in the dedup key) and C2 (make
  `candidates.last()` a hard error) remain unapplied Rust-seed changes.
- **Parent:** `compiler_cross_module_private_symbol_collision_2026-06-16`
- **Severity:** HIGH for the general mechanism (silent wrong answer, exit 0, JIT only).
  LOW for these four specific names — see verdict.

## Verdict summary

1. The collision mechanism **is a real silent wrong-answer defect on the JIT**
   (default engine). Reproduced from scratch. The interpreter is **correct**.
2. For the four sshd names specifically, the collisions are **currently benign**:
   every colliding pair differs in *parameter* types, which is exactly what the
   `$dupN` mangling keys on, so call sites resolve by exact match. And all
   `_hex_digit` definitions **agree on every in-range input** within their
   direction.
3. Therefore symbol collision is **NOT** a second cause of the `f`-read-as-`e`
   hex bug. That attribution to the seed parser stands. These four warnings are
   advisory **today**, but they sit one edit away from the live hole (below).

## 1. Enumeration (owned `src/**`, vendor excluded)

### `_hex_digit` — 11 definitions, 4 distinct signatures

| Signature | Files | Returns |
|---|---|---|
| `(i64) -> text` | `src/os/apps/sshd/ssh_hex.spl:1`, `src/lib/common/crypto/types.spl:37`, `src/lib/common/crypto/typed/ctypes.spl:15`, `src/lib/common/privilege/store.spl:40` | nibble → lowercase hex char (if/elif chain) |
| `(text) -> i64` | `src/os/kernel/net/embedded_certs.spl:9`, `src/app/ui.ipc/protocol.spl:428`, `src/app/ui.web/wm_quality_contract.spl:627` | hex char → nibble value (case-insensitive) |
| `(i32) -> text` | `src/os/tools/shell/hexdump/hexdump_tool.spl:58` (`digits.char_at(n & 0xF)`), `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl:85` (match arms) | nibble → hex char |
| `(u8) -> u8` | `src/os/crypto/dual_backend.spl:89` | nibble → ASCII **byte** (`0x30+n` / `0x61+n-10`) |
| `(i64) -> text` (variant) | `src/compiler/70.backend/linker/macho_parser.spl:80` | as above, but **fallthrough `return "f"`** — any `v > 15` also yields `"f"` |

**Do they disagree?** No, not on valid input. All four `(i64)->text` bodies map
14→`"e"`, 15→`"f"`; both `(i32)->text` bodies likewise; all three `(text)->i64`
bodies map `"e"/"E"`→14, `"f"/"F"`→15. Verified by reading each body's 14/15
arms. Only out-of-range differences exist: `hexdump_tool` masks (`n & 0xF`),
`macho_parser` returns `"f"` for anything ≥14 that isn't 14, others return
`"?"`/fall through. **No probe needed — they are input-equivalent in range.**

### `_u8_at` — 30+ definitions, 2 distinct signatures

- `([u8], u64) -> u8` — the overwhelming majority: all of `src/os/apps/sshd/*`
  (`ssh_mac`, `ssh_transport`, `ssh_packet`, `ssh_cipher`, `ssh_cipher_live`,
  `ssh_kex_primitives`, `ssh_session_helpers`), all of `src/os/crypto/*`
  (aes*, camellia, aria, zuc, sha256, whirlpool, ocb3, snow3g_sr, ed25519,
  rsa_fallback, …), `src/os/tls12/*`, `src/os/tls13/*`,
  `src/os/services/nvfs/core/crypto/aes128_gcm.spl:29`,
  `src/lib/common/crypto/aes_gcm.spl:19`. Returns `buf[idx]` bounds-guarded.
- `([u8], i64) -> u8` — **`src/os/crypto/curve25519_smalllimb.spl:15`** (sole
  outlier; `i64` index instead of `u64`).

The warning is caused entirely by that one outlier.

### `_cswap_pair` — 2 definitions

- `src/os/crypto/curve25519_smalllimb.spl:523` —
  `([u64],[u64],[u64],[u64], i64) -> X25519Swap4` (named struct)
- `src/os/crypto/curve25519.spl:409` —
  `(Fe25519,Fe25519,Fe25519,Fe25519, u64) -> (Fe25519,Fe25519,Fe25519,Fe25519)` (tuple)

Both conditional-swap the two projective point pairs; same arity (5).

### `_ladder_step` — 2 definitions

- `src/os/crypto/curve25519_smalllimb.spl:528` — `([u64] x5) -> X25519Step4`
- `src/os/crypto/curve25519.spl:446` — `(Fe25519 x5) -> (Fe25519 x4)`

Both are the Montgomery ladder differential-add-and-double step; same arity (5).

## 2. Mis-dispatch verdict — CONFIRMED on JIT, CLEAN on interpreter

Probe: `build/symcol_probe/` (`r_a.spl`, `r_b.spl`, `r_main.spl`). Two modules,
each with a private `_hex_digit`, **identical parameter types, differing return
types** (`(i64)->text` vs `(i64)->i64`), wildcard-imported (`use X.*`) so the
loader flattens them into one namespace.

```
$ bin/simple run r_main.spl          # JIT (default)
warning: private helper `_hex_digit` has 2 co-compiled definitions ... [compiler_cross_module_private_symbol_collision]
b_val(15) expect 1500 => 1500
EXIT=0
                                     # a_val(15) line SILENTLY DROPPED

$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r_main.spl
a_val(15) expect f    => f           # CORRECT
b_val(15) expect 1500 => 1500
```

| Engine | Result |
|---|---|
| **JIT (default)** | **MIS-DISPATCHES.** `a_val` binds to the `(i64)->i64` body; the text interpolation of the resulting i64 collapses and the whole `print` line vanishes. **Exit code 0. No error. Silent.** |
| **Interpreter** | Correct. Both calls hit their own module's helper. |

Note the inversion of the usual assumption: the interpreter's `func_table` is a
bare-name last-write-wins map (`src/compiler/10.frontend/core/interpreter/eval_tables.spl:172`)
and *should* be the fragile one, but in practice import scoping keeps it right;
the JIT's mangling scheme is what leaks.

### Root cause of the JIT hole

`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1234-1260` builds
`private_dup_overloads` from **parameter types only** — the return type is not
part of the key:

```rust
let sig: Vec<TypeId> = func.params.iter().filter(|p| p.name != "self").map(|p| p.ty).collect();
...
if sigs.len() < 2 || sigs.iter().all(|s| s == &sigs[0]) {
    continue;   // "last-write-wins stays observably equivalent" — FALSE when returns differ
}
```

When two definitions share parameter types but differ in return type, no `$dupN`
variants are emitted at all and one body is silently overwritten. The comment
asserting observable equivalence is wrong.

Second, weaker hole at the call site
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:557-577`):
resolution is exact-param-type match, then `by_arity` (only if it singles out
**one** candidate), then an explicit `candidates.last()` fallback — i.e.
deliberate last-write-wins. Every one of the four names has **all candidates at
the same arity** (`_hex_digit` arity 1; `_u8_at` arity 2; `_cswap_pair` and
`_ladder_step` arity 5), so `by_arity` can never disambiguate any of them. They
are protected *solely* by exact param-type match. Any call site where an
argument infers as `Any`, or where an integer width is inferred differently than
declared, drops straight to `candidates.last()` and gets the wrong body.

## 3. Independence from the parser bug

**Independent mechanism, but NOT a second cause of the observed hex bug.** The
reported symptom (every `f` decoded as `e`) cannot be produced by any dispatch
choice among the enumerated definitions, because every `_hex_digit` body agrees
on `"e"`→14 and `"f"`→15. A cross-direction mis-dispatch (a `(text)->i64` call
landing on `(i64)->text` or `(u8)->u8`) would produce garbage or a crash, not a
consistent off-by-one. The seed-parser attribution stands unchallenged.

## 4. Proposed remedy — NOT applied

Compiler-side (file separately, do not touch while lanes are live):

- **C1 (real bug):** include the return type in the `private_dup_overloads`
  signature key in `lowering_core.rs`, so return-type-only collisions also get
  `$dupN` variants. This is the confirmed silent-wrong-answer hole.
- **C2:** make the `candidates.last()` fallback in `lowering_expr_call.rs` a hard
  compile error rather than a silent guess. A guess here is unrecoverable.

Source-side renames to defuse these four warnings (each is a one-file, one-symbol
change; **proposed, not done**):

| Rename | Where | Defuses |
|---|---|---|
| `_u8_at` → `_u8_at_i` | `src/os/crypto/curve25519_smalllimb.spl:15` (sole `i64`-index outlier; ~4 call sites in that file) | `_u8_at` entirely |
| `_cswap_pair` → `_cswap_pair_limb`, `_ladder_step` → `_ladder_step_limb` | `src/os/crypto/curve25519_smalllimb.spl:523,528` | both, entirely |
| `_hex_digit` → `_hex_digit_byte` | `src/os/crypto/dual_backend.spl:89` (the odd `(u8)->u8` one; already has a `_hex_digit_text` sibling, so the name is misleading anyway) | removes the most-divergent variant |
| `_hex_digit` → `_hex_from_char` | the three `(text)->i64` decoders (`embedded_certs.spl:9`, `protocol.spl:428`, `wm_quality_contract.spl:627`) | splits encoder/decoder namespaces — highest value, since the two directions sharing one name is what makes a fallback hit catastrophic |

Recommended order: the three `curve25519_smalllimb` renames first (fully removes
3 of the 4 warnings, single file, no cross-module churn).

## Reproduction

`build/symcol_probe/` — `r_a.spl` / `r_b.spl` / `r_main.spl` is the minimal
mis-dispatch case. `mod_a/b/c.spl` + `main.spl`/`main2.spl` and
`chain_a/b.spl` + `chain_main.spl` are negative controls: **selective (`use m.f`)
and plain (`use m`) imports do not flatten**, emit no warning, and dispatch
correctly on both engines. Only wildcard `use m.*` (and the spec harness's
equivalent) triggers the flattening that exposes the bug.

---

## Re-verification 2026-08-17 (compiler-lint lane) — OPEN, but the file attribution is WRONG

The tracking row files this against `src/compiler/35.semantics/resolve.spl`.
That is incorrect and would send the next lane to the wrong file:

- `grep -n candidates src/compiler/35.semantics/resolve.spl` returns **one**
  line (869) and it is a comment about method-vs-global fallthrough. There is
  no `candidates.last()` fallback and no overload dedup key in that file.
- Both remaining remedies live in the **Rust seed**, not in `35.semantics`:
  - **C1** (include the return type in the dedup key) —
    `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1642-1734`,
    where `private_dup_overloads: HashMap<String, Vec<(Vec<TypeId>, String)>>`
    (declared at `lowering_core.rs:295`) is built keyed on **parameter** types
    only.
  - **C2** (make the `candidates.last()` fallback a hard error) —
    `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:640-645`.

Both files are under `hir/lower` / MIR-lowering trees that are explicitly
claimed by other concurrent lanes, so **no change was made here.**

Independent live confirmation that the mechanism is still active: an unrelated
single-file `bin/simple lint` run on 2026-08-17 emitted
`compiler_cross_module_private_symbol_collision` warnings for `dir_remove_all`
((text)->bool vs (text)->i32), `file_read_bytes` ((text)->[i64] vs (text)->[u8]),
`join_path`, `last_index_of`, `read_file`, `shell`, and `write_file` — every one
of them a pair that **differs only in RETURN type or in a String/text pairing**,
i.e. exactly the class C1's parameter-only dedup key cannot separate. This is
stronger evidence than the original sshd four names, which the doc itself
classifies as benign.

**Verdict: OPEN (C1/C2), OUT-OF-SCOPE for this lane.** Refile against
`src/compiler_rust/compiler/src/mir/lower/{lowering_core.rs,lowering_expr_call.rs}`.
Not proven here: that any of the seven names above is actually mis-dispatched at
runtime — the warning proves the ambiguity exists, not that a fallback was hit.

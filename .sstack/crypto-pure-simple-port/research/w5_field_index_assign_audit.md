# W-5 Audit: caller-side `obj.field[i] = x` in security-relevant subtree

Wave: `crypto-pure-simple-port` wave 3.
Bug under audit: **interpreter silently drops** `obj.field[i] = x` /
`g_state.field[i] = x` (struct-field index-assign on struct/global). Per
the orchestrator brief this is tracked in
`doc/08_tracking/bug/bug_interpreter_struct_field_index_assign_2026-04-25.md`
(see also `bug_csprng_rekey_silent_noop_2026-04-26.md`).

> **Caveat for reviewer.** Both bug docs cited above and the constructor-rebind
> exemplar `src/lib/common/math/bignum/fixed.spl:404` are NOT present in this
> branch's working tree at audit time. `git log --all -- '**/bug_interpreter_struct_field_index*'`
> returned 0 commits; `'**/bug_csprng_rekey_silent_noop*'` returned 0; the
> bignum subtree itself is missing from `src/lib/common/`. Wave-2 work has not
> landed in this branch — only `random.spl` has the constructor-rebind fix
> applied as a WC mod (W-1's turf). The 7-row "Confirmed scope" classification
> table the brief refers to was therefore not consulted for this audit; B/S/R
> classification below is by intuition aligned with the documented pattern
> ("caller-side or module-global" = B; "inside-fn-then-return" = S).
> **Action for orchestrator:** confirm whether wave-2 docs need to be
> rebased/cherry-picked into this branch before declaring wave-3 done.

## Scan methodology

Two regex passes over each in-scope directory:

1. **Primary** (per brief):
   `^[[:space:]]+([A-Za-z_][A-Za-z0-9_]*|self)\.[A-Za-z_][A-Za-z0-9_]*\[[^]]+\][[:space:]]*=[^=]`
2. **Variant 1 — multi-line value** (LHS-only on the line):
   `\.\w+\[[^]]+\][[:space:]]*=[[:space:]]*$`
3. **Variant 2 — chained / indexed receivers** (`].field[i] = x`):
   `\][[:space:]]*\.[A-Za-z_][A-Za-z0-9_]*\[[^]]+\][[:space:]]*=[^=]`

All three across:
- `src/os/crypto/` (excl. W-1's `random.spl`)
- `src/os/apps/sshd/` (USER WC — read-only)
- `src/os/tls13/`
- `src/lib/nogc_sync_mut/tls/`
- `src/lib/common/{cert,bcrypt,scrypt,jwt,signature,secure_random,crypto}/`

## Hit count

**Total raw hits: 1** (all variants combined).
**Code-level hits after docstring elimination: 0.**

| Directory | Files (.spl) | Raw hits | Code hits |
|-----------|--------------|----------|-----------|
| `src/os/crypto/` | 17 | 1 (in `random.spl`) | 0 |
| `src/os/apps/sshd/` | 12 | 0 | 0 |
| `src/os/tls13/` | 9 | 0 | 0 |
| `src/lib/nogc_sync_mut/tls/` | 7 | 0 | 0 |
| `src/lib/common/cert/` | 7 | 0 | 0 |
| `src/lib/common/bcrypt/` | 7 | 0 | 0 |
| `src/lib/common/scrypt/` | 7 | 0 | 0 |
| `src/lib/common/jwt/` | 7 | 0 | 0 |
| `src/lib/common/signature/` | 7 | 0 | 0 |
| `src/lib/common/secure_random/` | 8 | 0 | 0 |
| `src/lib/common/crypto/` | 8 | 0 | 0 |
| **TOTAL** | **96** | **1** | **0** |

## Classification table

| File:Line | Hit text | Class | Rationale |
|-----------|----------|-------|-----------|
| `src/os/crypto/random.spl:249` | `g_csprng.key[i] = g_csprng.key[i] ^ word` (docstring) | **N/A (docstring false-positive)** | Line 249 is inside a triple-quoted docstring of `_csprng_xor_in_seed_bytes`. The string quotes the *bug pattern* in explanatory prose. The actual code at line 273 is `new_key.push(g_csprng.key[i] ^ word)` followed by wholesale rebind `g_csprng.key = new_key` at line 277 — **constructor-rebind already applied** by W-1 in WC. |

A second docstring hit at `random.spl:204` (matched by an extra-broad pass)
is similarly a docstring quote in `_csprng_install_seed_bytes`, also
documenting the workaround.

## (B) hits I fixed

**None.** The audit returned no code-level (B) hits in W-5's fix scope.

## (R) ambiguous hits

**None.**

## (B) hits in user-WC (sshd) flagged for user

**None.** `src/os/apps/sshd/` returned 0 hits across all three regex variants.
The sshd modules use receive/parse/build idioms that produce values via
returns rather than mutating struct fields by index after construction —
which is consistent with the "inside-fn-then-return" pattern that is **S**afe
under the bug.

## Verification commands (rerunable)

```bash
# Primary pattern, all dirs
for d in \
    src/os/crypto src/os/apps/sshd src/os/tls13 \
    src/lib/nogc_sync_mut/tls \
    src/lib/common/cert src/lib/common/bcrypt src/lib/common/scrypt \
    src/lib/common/jwt src/lib/common/signature \
    src/lib/common/secure_random src/lib/common/crypto; do
  grep -rnE '^[[:space:]]+([A-Za-z_][A-Za-z0-9_]*|self)\.[A-Za-z_][A-Za-z0-9_]*\[[^]]+\][[:space:]]*=[^=]' "$d/" 2>/dev/null
done

# Variant 1 — multi-line value
... (same dirs) grep -rnE '\.\w+\[[^]]+\][[:space:]]*=[[:space:]]*$'

# Variant 2 — chained receiver
... (same dirs) grep -rnE '\][[:space:]]*\.[A-Za-z_][A-Za-z0-9_]*\[[^]]+\][[:space:]]*=[^=]'
```

All three commands return only `random.spl:249` (docstring) on the
current `HEAD` + `random.spl` WC mod. A second docstring hit at
`random.spl:204` is matched only by the broader pass that drops the
leading-whitespace anchor (it appears in `_csprng_install_seed_bytes`'s
docstring quoting the same bug pattern). Both are prose, not code.

### Sanity-check: `tls13/` and `nogc_sync_mut/tls/` are non-empty

To rule out "audited and clean = nothing to audit", I confirmed these two
dirs have real state-mutation idioms — just *not* the index-assign form:

```
$ wc -l src/os/tls13/*.spl src/lib/nogc_sync_mut/tls/*.spl | tail -1
   5107 total
$ grep -rnE '\.[A-Za-z_][A-Za-z0-9_]*[[:space:]]*=[^=]' \
    src/os/tls13/ src/lib/nogc_sync_mut/tls/ | wc -l
7
```

The 7 hits are all *whole-field* assigns of the form
`config.listen = ...` / `config.accept_count = n` (in `test_server_config.spl`)
or pattern-match equality (`if val CertVerifyResult.Ok = verify_result:`),
none of them index-assign. **Verified:** these dirs follow a
returns-or-whole-rebind idiom and are genuinely free of the bug pattern,
not empty scaffolding.

## Conclusions

1. **The bug surface in W-5's scope is empty.** No code-level B/S/R hits.
2. **W-1's WC change to `random.spl`** already contains the only
   constructor-rebind fix needed in `src/os/crypto/`, with inline reference
   to `bug_csprng_rekey_silent_noop_2026-04-26`.
3. **`src/os/apps/sshd/` is clean** of this bug pattern. No fixes needed
   there for *this* class of issue (the noted M1/AES-GCM rewrites and
   `ssh_put_text` ASCII bug from `m_status.md` are different defects, not
   in W-5's audit charter).
4. **Acceptance gate:** the brief's "deliberate-fail proof on at least one
   (B) fix" is **moot** with zero (B) hits. No regression spec was added,
   to avoid manufacturing a fix target. Per advisor guidance, this is
   documented rather than silently skipped.
5. **Blocker on full classification confidence:** the cited 7-row
   "Confirmed scope" table in `bug_interpreter_struct_field_index_assign_2026-04-25.md`
   is unavailable in this branch. Re-running the audit against that
   table once it lands is recommended; the classification herein assumes
   the documented pattern's plain reading.

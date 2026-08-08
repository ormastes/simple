# Module-level `val` reads wrong inside credential store — a constant-only path returns an out-of-band value

- **Filed:** 2026-08-08
- **Severity:** MED (silently wrong constants; here it mis-set a KDF cost factor)
- **Area:** compiler / `src/lib/nogc_sync_mut/terminal/credential/store.spl`

## What is wrong

`credential_kdf_cost()` returns the BCrypt cost factor. With
`SIMPLE_CREDENTIAL_KDF_COST` **unset**, it takes a path that reads no input at
all — it returns the module-level constant `BCRYPT_COST`, declared

```
val BCRYPT_COST: i64 = 10
```

The spec asserts only that the result lies in `4..=16`. It **fails**: the
function returns a value outside that band on a path whose sole source of data
is that constant.

## Evidence

`test/01_unit/lib/terminal/credential_key_file_format_spec.spl`, case
*"resolves a cost inside the accepted band by default"*:

```
SPEC FILE VERDICT: ... declared>=12 executed=12 passed=11 failed=1 dropped=0
  ✗ resolves a cost inside the accepted band by default
```

## What was ruled out

**Early returns / control flow — REFUTED.** The first revision used early
returns:

```
val trimmed = rt_env_get(BCRYPT_COST_ENV).trim()
if trimmed.length() == 0:
    return BCRYPT_COST
...
```

It was rewritten to a single exit with clamp-by-construction
(`var cost = BCRYPT_COST` … only ever assigning an in-band value). **The
rewrite failed identically** — same case, same verdict, `passed=11 failed=1`.

Early returns are independently proven to work in this same module: four cases
in the same spec file pass and each depends on one firing —
`credential_key_generate`'s legacy-key refusal (`return false`), its empty
passphrase check (`return false`), and `credential_load_key`'s short-key and
missing-file guards (`return []`).

So neither control flow nor the function's logic explains it. What remains is
the **module-level `val` read** itself. Note the clamp rewrite also reads
`BCRYPT_COST_MIN` / `BCRYPT_COST_MAX`; if those read as `0` the band check
degenerates and the seed value is wrong too, which fits the observation.

This resembles the known family in
`.claude/memory/reference_jit_module_level_val_from_function_call_reads_zero.md`
(module globals reading zero), but that entry is about the `--native` lane and
this reproduces on the **interpreter** path under `bin/simple test`.

## Workaround in place

`credential_kdf_cost()` now writes the default and the band as **literals**
(`10`, `4`, `16`) rather than reading the constants. The named constants are
retained as the documented contract. There is a comment in the function saying
not to "tidy" the literals back into the constants until this is fixed.

## Reproduce / next step

Narrow it with a minimal spec in its own file: a module with
`val K: i64 = 10` and `fn get_k() -> i64: K`, asserting `get_k() == 10`. Then
widen to a module of the size of `store.spl` (it declares ~14 module-level
`val`s) to see whether count, position, or a specific declaration triggers it.
Print the actual returned value — this bug doc records only that the value is
out of band, not what it is, because the assertion is a range check.

## See also

- `doc/09_report/lib/crypto/credential_store_aes_cbc_adversarial_review_2026-08-08.md` (finding F6)
- `doc/08_tracking/bug/credential_kdf_multi_derivation_spec_aborts_runner_2026-08-08.md`

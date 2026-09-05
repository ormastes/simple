# credential_kdf_cost returns the wrong value on a path that cannot — three implementations refuted

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

**Module-level `val` reads — ALSO REFUTED.** The function was rewritten a
third time with the default and the band as bare **literals**
(`var cost = 10` … `if parsed >= 4 and parsed <= 16`), reading no module
constant at all and inlining the env-var name. **It failed identically again**
— `passed=11 failed=1`, same case.

So all three implementations fail: early-return, single-exit clamp, and
literals-only. With the env var unset, the literal version reduces to
`var cost = 10; if "".length() > 0: …; cost` — which cannot return anything but
10. That the assertion still fails means the fault is **not in
`credential_kdf_cost`'s body at all**. Remaining candidates, none yet tested:

- `rt_env_get` on an **unset** key does not return an empty string (it may
  return nil, or an error string), so `.trim().length() > 0` is true and the
  `to_i64()` branch runs on garbage;
- the spec-side assertion form. The original case asserted
  `expect(c >= 4).to_equal(true)` — a comparison expression on an i64 returned
  across a module boundary.

This resembles the known family in
`.claude/memory/reference_jit_module_level_val_from_function_call_reads_zero.md`
(module globals reading zero), but that entry is about the `--native` lane and
this reproduces on the **interpreter** path under `bin/simple test`.

## State in tree

`credential_kdf_cost()` currently uses literals. The named constants
(`BCRYPT_COST`, `BCRYPT_COST_MIN`, `BCRYPT_COST_MAX`) are retained as the
documented contract. The literals are NOT known to help — they were the third
refuted attempt — so this is not a workaround, just the current form.

The spec case is left **deliberately RED** as a live record of the defect,
per `.claude/rules/testing.md`: a correct spec that fails is a legitimate
artifact and must not be weakened to pass.

## Next step — MEASURE before changing anything else

The single reason three implementations were tried blind is that the original
assertion was a range check (`expect(c >= 4).to_equal(true)`), which reports
only "false". It is now
`expect(credential_kdf_cost()).to_equal(10)`, so the next run prints the value
actually received. **Read that number first.**

- If it is `0` → a constant/return read is landing as zero; narrow with a
  minimal module (`val K: i64 = 10` + `fn get_k() -> i64: K`).
- If it is some parse of an env string → `rt_env_get` does not return `""` for
  an unset key; check its unset-key contract in the runtime extern table.
  `rt_env_get` is declared `-> text` in four `.spl` modules, so a nil return
  would be a type-contract violation worth its own bug.
- If it is `10` → the defect is in the assertion path, not the function, and
  the range-comparison form is the thing to file.

## See also

- `doc/09_report/lib/crypto/credential_store_aes_cbc_adversarial_review_2026-08-08.md` (finding F6)
- `doc/08_tracking/bug/credential_kdf_multi_derivation_spec_aborts_runner_2026-08-08.md`

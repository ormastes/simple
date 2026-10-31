# Seed native build mis-dispatches `text.split` when one module mixes arities (2026-11-01)

Status: OPEN. Root-caused by the devhub-native-config-read lane on
2026-11-01 against the seed-built devhub artifact
(`build/devhub-goal/artifacts/seed/devhub`, Rust seed
`src/compiler_rust/target/bootstrap/simple`, `--backend cranelift`,
`--runtime-bundle core-c-bootstrap`; seed skips `--mode dynload` and emits
`one-binary`).

## Symptom

The seed-built NATIVE devhub binary cannot read `~/.config/devhub/auth.sdn`:
`devhub minio health` prints `error: MinIO URL not configured` (exit 1) even
when the file exists and contains a valid `[minio]` section. The identical
sources under the seed INTERPRETER read and parse the config correctly.

Reproduced independently of devhub with a one-module probe:

```spl
fn main() -> i64:
    val content = "[minio]\nurl = http://127.0.0.1:1\n"
    val lines = content.split("\n")        # 2-arg split
    for raw in lines:
        val line = raw.trim()
        if line.contains("="):
            val parts = line.split("=", 2) # 3-arg (limit) split
            print "parts={parts.len()}"    # native: 0  /  interp: 2
    0
```

Native prints `parts=0`; the interpreter prints `parts=2`. A module that uses
ONLY ONE of the two arities works natively (both the 2-arg-only
`auth_token_store.spl` native fixture and a 3-arg-only probe pass); whichever
arity is used second in a module that mixes them silently returns an empty
array (observed in both orders).

## Root cause

The seed interpreter dispatches `split` with an optional limit argument
(`compiler/src/interpreter_method/string.rs`, `"split"` arm: `splitn` when
`limit > 0`). The native (Cranelift/instr) lowering has no single coherent
dispatch for the two arities: the builtin registry declares only the
1-parameter `split -> rt_string_split`
(`compiler/src/method_registry/builtins.rs`), the instr backend maps the bare
name `"split" -> rt_string_split` (`codegen/instr/calls.rs`), and
`rt_string_split_limit` is declared in `codegen/runtime_sffi.rs` but never
referenced by any lowering path. When a Simple module contains call sites for
BOTH arities, the native symbol resolution/mangling collapses or re-binds one
arity to the wrong co-compiled target and the mis-bound call yields an empty
array at runtime (no compile or link error).

NOT the cause (ruled out by strace + probes): the sosix env/file facade ABI.
The native binary opens and reads `auth.sdn` correctly (3 openat + read of the
exact bytes); `sosix_env_get("HOME")` returns the right value natively.

## Impact

Any native-built module that mixes `text.split(sep)` and `text.split(sep, n)`
call sites has the second-used arity silently broken (returns `[]`), which
corrupts parsing logic without any diagnostic. In devhub this made
`adapter_minio._parse_minio_section` return the default config
(`load_minio_config` at `src/app/devhub/adapter_minio.spl`), failing
`test/03_system/app/devhub/feature/minio_binary_put_spec.spl` ("should retain
failure status when health output is JSON").

## Workaround

All sites split at the FIRST separator only, so each replaces its
`(sep, limit)` call with `cut(s, sep)` from `std.common.text_advanced`
(first-separator split, implemented with the single-arity `split`
internally), leaving every touched module single-arity. Tagged
`@workaround bug=seed-native-split-overload-collision-20261101` at each
site:

- `src/app/devhub/adapter_minio.spl` `_parse_minio_section` (`key = value`
  lines of the `[minio]` auth.sdn section; the originally reported failure).
- `src/app/devhub/cmd_daily_debug.spl` `_looks_like_jira_key` (`PROJECT-123`
  token check; remainder after the first `-` keeps further dashes, matching
  `split("-", 2)`).
- `src/app/devhub/cmd_outlook.spl` outlook section parser (`key: value`
  lines of auth.sdn; same first-colon fix as config.spl).
- `src/app/devhub/email_translate.spl` `_classify_query_token` (`op:value`
  Gmail query tokens; the remainder after the first `:` keeps further
  colons, matching `split(":", 2)`).

## Suspected owner

Seed compiler native codegen / method dispatch:
`src/compiler_rust/compiler/src/method_registry/builtins.rs`,
`src/compiler_rust/compiler/src/codegen/instr/calls.rs`,
`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs` (builtin
bare-name guard list contains `split` at mangle.rs:1426).

## Removal condition

Retire when the seed (or a self-hosted stage2 containing the fix) lowers both
`text.split` arities to their correct runtime targets (`rt_string_split` /
`rt_string_split_limit`) in one module. Then revert all four `cut()`
workarounds (adapter_minio.spl, cmd_daily_debug.spl, cmd_outlook.spl,
email_translate.spl) and re-run `minio_binary_put_spec.spl` plus the
cmd_daily_debug/email_translate/cmd_outlook unit specs against a seed-built
native devhub artifact.

# The whole `rt_package_*` raw-C-ABI extern family fails from the JIT — 0600 on the credential key is fiction

- **Filed:** 2026-08-08
- **Severity:** CRITICAL (the only at-rest control on the AES key is absent; key lands 0664)
- **Status:** runtime defect OPEN. Caller contract made honest in
  `src/lib/nogc_sync_mut/terminal/credential/store.spl` (this doc).
- **Area:** compiler seed JIT extern dispatch / `src/compiler_rust/runtime/src/value/sffi/package.rs`

## REFUTED premise, stated plainly

The review that prompted this said *"No C implementation of `rt_package_chmod`
exists under `src/runtime/`."* **That is wrong.** A real, correct implementation
exists and is exported:

```
src/compiler_rust/runtime/src/value/sffi/package.rs:330
    #[no_mangle] pub unsafe extern "C" fn rt_package_chmod(file_path: *const c_char, mode: u32) -> i32
```

It CStr-decodes the path, builds `fs::Permissions::from_mode(mode)`, calls
`fs::set_permissions`, and returns 0/-1. It is declared in
`src/compiler_rust/compiler/src/interpreter_extern/package.rs:19`, registered
twice in `interpreter_extern/mod.rs` (1534, 2401), listed in
`common/src/runtime_symbols.rs:1755`, and exported in the runtime symbol table.
There is nothing missing and nothing to write.

## What is actually wrong

The call never reaches that implementation with a usable argument. Measured
from the JIT (`bin/simple run`, deployed seed, 2026-08-08):

| probe | result | expected |
|---|---|---|
| `rt_file_write_text(abs_path, "x")` | `true` | true |
| `rt_package_chmod(abs_path, 0o600)` | `4294967295` | 0 |
| `rt_package_chmod(abs_path, 384)` | `4294967295` | 0 |
| `rt_package_chmod(abs_path, 420)` | `4294967295` | 0 |
| `rt_package_chmod(rel_path, 0o600)` | `4294967295` | 0 |
| `rt_package_chmod(shell_created_file, 0o600)` | `4294967295` | 0 |
| on-disk mode after all of the above | `0664` (`-rw-rw-r--`) | `0600` |
| **`rt_package_exists(existing_file)`** | **`0`** | 1 |
| `rt_file_exists(same_file)` (Simple-aware extern) | `true` | true |

The last two rows are the discriminator. `rt_package_exists` answering **0 for
a file that demonstrably exists** — while the registered `rt_file_exists`
answers `true` on the identical path in the same run — shows this is not a
chmod bug. **The entire `rt_package_*` raw-C-ABI family mis-marshals its `text`
argument when dispatched from the JIT**, so `CStr::from_ptr` does not receive a
valid C string and every call in the family fails closed.

`4294967295` is `-1` widened as `u32`: the `-> i32` return is also mis-marshalled
on the way back, so callers comparing `== -1` will not match either.

Two more registered externs are simply **absent from the deployed seed** —
calling them logs `unknown extern function` and yields a default:

- `rt_file_mode` → returns 0, so any spec asserting the real on-disk mode is
  vacuous
- `rt_file_atomic_write_mode` → returns `false`, so the write-with-mode fix
  cannot be adopted at any call site until the seed is redeployed

## Impact

`~/.simple/credential_key` **is** the AES-256 key — its content is the secret,
so the file mode is the only at-rest control there is. It lands `0664`:
group- and world-readable. `rt_package_chmod(dir_path, 0o700)` on `~/.simple`
is a no-op for the same reason, so the containing directory is not narrowed
either.

## The caller contract was dishonest in both directions

`credential_key_generate` ended with

```
rt_package_chmod(path, KEY_FILE_MODE) == 0
```

so it returned **false** — "generation failed" — *after* having already written
the key, and left the 0664 file sitting there. The caller was told nothing was
generated while an unprotected key existed on disk. Worst of both.

## What was changed here (no fabricated implementation)

No stub was written and no runtime code was touched. The call site now fails
honestly:

```
if rt_package_chmod(path, KEY_FILE_MODE) != 0:
    rt_file_delete(path)
    return false
true
```

`rt_file_delete` is a Simple-aware registered extern and is verified working on
the deployed seed (`DELETE=true`, `EXISTS_AFTER=false`). So a `false` return now
guarantees **no unprotected key file was left behind**, which is the only
correct behaviour while the mode cannot be applied. On the deployed seed this
means key generation is impossible — that is the accurate state of the world,
not a regression introduced here.

`!= 0` is used rather than `== -1` deliberately, because the return arrives as
`4294967295`.

## Positive control

End-to-end probe after the change: `GEN=false`, and `ls` confirms **no key file
remains**. Before the change the same probe left a `-rw-rw-r--` key file on disk
while also reporting `false`.

## Fix directions (runtime, not filed as done)

1. Fix `text` argument marshalling for raw-C-ABI externs from the JIT, or route
   the `rt_package_*` family through the Simple-aware extern table the way
   `rt_file_*` is routed.
2. Redeploy the seed so `rt_file_atomic_write_mode` exists, then adopt it at the
   key-write call site — it applies the mode to a same-directory temp before the
   secret is written, removing the write-then-chmod window entirely. See
   `credential_key_file_write_has_no_mode_argument_2026-08-08.md`.
3. Restore `rt_file_mode` so on-disk mode assertions stop being vacuous.

## Related

- `doc/08_tracking/bug/credential_key_file_write_has_no_mode_argument_2026-08-08.md` (the write-then-chmod window; its atomic-write fix is blocked on the seed redeploy)
- `doc/08_tracking/bug/credential_store_key_and_salt_corrupted_by_list_param_hex_2026-08-08.md`
- `doc/08_tracking/bug/credential_key_generate_random_hex_length_reads_shifted_2026-08-08.md`

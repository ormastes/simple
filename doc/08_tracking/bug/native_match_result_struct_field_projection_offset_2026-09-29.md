# Native Result match shifts struct field projections

The Target 6 compact output index native spec fails while assembling a typed-HIR export SMF. `cold_hir_reverse_projection_v1` constructs `ColdHirReverseProjectionV1(payload, section, digest, dependents)` and returns it as `Ok(...)`. In `cold_hir_export_smf_from_seed_bytes_v1`, a `match` expression binds the `Ok(projection)` value to `reverse`.

On the AArch64 native binary, GDB at the caller shows the returned struct's fields in declaration order: field 0 is a valid 69-byte text payload, field 1 is the section record. The generated caller loads `reverse.payload` from offset 8 and `reverse.digest` from offset 24, one field later than their actual offsets 0 and 16. The section record is consequently passed as payload. The SMF validator reports a reverse-projection section of 3 bytes with expected SHA-256 for empty text, although the producer's payload has 69 bytes.

The compiler must preserve struct layout when a `Result<Struct, text>` is unwrapped through a match expression. Changing this call site to explicit `is_err()`/`unwrap()` moved the native spec past SMF assembly, but all four examples now fail in the later draft check with `cold-drafts-reverse-projection-mismatch:a`. That later path already uses explicit `unwrap()`, so this evidence does not prove the match expression is the only cause. Add a minimal native compiler regression for field 0 and a later field after both `match Ok(value): value` and explicit `unwrap()`. Inspect the draft's recomputed projection and artifact digest before attributing its mismatch to layout.

The native SPipe runner currently exits 0 even when all four examples fail; see `native_sspec_four_failures_exit_zero_2026-09-29.md`. Read its textual verdict, not just the process status.

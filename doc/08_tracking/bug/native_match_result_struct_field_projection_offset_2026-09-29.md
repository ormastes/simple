# Native Result match shifts struct field projections

The Target 6 compact output index native spec fails while assembling a typed-HIR export SMF. `cold_hir_reverse_projection_v1` constructs `ColdHirReverseProjectionV1(payload, section, digest, dependents)` and returns it as `Ok(...)`. In `cold_hir_export_smf_from_seed_bytes_v1`, a `match` expression binds the `Ok(projection)` value to `reverse`.

On the AArch64 native binary, GDB at the caller shows the returned struct's fields in declaration order: field 0 is a valid 69-byte text payload, field 1 is the section record. The generated caller loads `reverse.payload` from offset 8 and `reverse.digest` from offset 24, one field later than their actual offsets 0 and 16. The section record is consequently passed as payload. The SMF validator reports a reverse-projection section of 3 bytes with expected SHA-256 for empty text, although the producer's payload has 69 bytes.

The compiler must preserve struct layout when a `Result<Struct, text>` is unwrapped through a match expression. Changing this call site to explicit `is_err()`/`unwrap()` moved the native spec past SMF assembly. In the later draft check, GDB showed the recomputed reverse digest matched the section digest while the artifact's reverse digest was zero. That artifact was also built from a `match Ok(value): value` struct binding; changing it to explicit unwrap moved the spec past the draft check. Add a minimal native compiler regression for field 0 and a later field after `match Ok(value): value`, then fix lowering and remove both workarounds once that passes.

The native SPipe runner currently exits 0 even when all four examples fail; see `native_sspec_four_failures_exit_zero_2026-09-29.md`. Read its textual verdict, not just the process status.

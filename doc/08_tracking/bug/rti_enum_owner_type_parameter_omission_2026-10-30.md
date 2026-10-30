# Generic enum owner binders omitted from return-type interface rows

The admitted11 lifetime probe failed before executing its body. The retained log `/tmp/simple-worker-surface-lifetime-admitted11-20261030/build.log` reports `E-RTI-007` for `lib.nogc_async_mut.async.poll` / `enum:Poll::unwrap`: type parameter T is not bound by the callable or owner.

`Poll<T>` and its HIR enum declaration carry T. Its `unwrap` method has return T but no method-local generic parameters. `rti_owner_type_params` scans only struct and class declarations, so it hands an empty owner binder list to `rti_row_from_signature_v1`. The strict RTI conversion correctly rejects T. The compact declaration path repeats the omission in `mir_declaration_rti_owner_params_v1`.

Repair both collectors to read enum declaration type parameters. Preserve method-local-then-owner binder ordering and every RTI validation error. Do not infer binders from a return type or suppress generic enum rows. No change to Poll, the runtime, or entry closure selection is needed.

Coverage adds actual source parsing/HIR rows, concrete i64/bool instantiation with owner and method-local binders, malformed-owner negative control (E-RTI-007), and compact/full row equality. The native fixture checks returned values through generic enum methods. Runtime execution is pending the build owner's next changed-producer lane; this source repair is not a native qualification claim.

Source base: b5b650fc231b7a46152b446976db723c5bd32899. Failing producer: bdd4c38529e44a86b78f183f7efdbc985faf26d67eb313ed6f8411e67e9d8a60. Active frozen attempt12 was not modified. Separate table-fill dependency repair 481c4eadf31 is independent.

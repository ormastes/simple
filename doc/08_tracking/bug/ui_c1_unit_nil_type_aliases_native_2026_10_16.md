# UI C1 native dependency type-name compatibility

Status: source repair prepared; runtime verification pending. Authoritative bug
database reconciliation is pending because no qualified full CLI is available.

The exact 0CD6 producer, compiling frozen C1, reports unresolved `Unit` and
`Nil` types in the UI closure. Its HIR type lowering recognizes lowercase
`unit` and `void` as `HirTypeKind.Unit`; uppercase names require declarations.

The affected `Unit` annotations belong to `Result<Unit, E>` signatures in
`wm_bridge.spl`, `bounded_channel.spl`, and the HostTaskbarRuntime owner.
Successful branches return `Ok(())`. Dependent modules repeat the unresolved
type diagnostic when importing these signatures. The repair uses canonical
`unit` only in those type arguments and preserves all function bodies.

The only affected `Nil` annotation is the callback return in JS `array_forEach`.
Its callback result is discarded and the function is a side-effect loop. It
does not construct or transport a `JsValue.Nil`. Canonical `unit` describes
that callback contract without introducing a runtime sentinel or nominal type.

Recovery reference: `c1f630e7a05d539852f53444231d4f90fd76d6a4`.
The source compatibility tags identify the exact changed signatures. Do not
revert them merely after fetching a compiler alias change; require an admitted
producer and actual regression evidence first.

Evidence: `phase4-ui-0cd6-c1f6-cycle2/terminal-failure-analysis` under the shared
bootstrap evidence root. The UI lane has used two of three verification
attempts. No third attempt has been launched for this repair.

# Checked startup initializer discovery

Source: `test/01_unit/compiler/backend/xray_initializer_discovery_spec.spl`.
Status: authored; full Simple spec execution pending.

The real checked symbol-discovery owner accepts an empty object list and rejects the deliberately non-object fixture. The latter also fails closed when the host symbol tool is unavailable; it is not evidence that a particular tool ran. The enabled tracing entry path uses this checked owner and propagates its failure before generating a readiness marker. Successful discovery does not establish initializer dependency order, complete source semantics, or observer admission.

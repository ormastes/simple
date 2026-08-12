# MCI-v2 Rendering Producer Shell Contract

Run `sh test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs`.

The host-only unit contract creates signed controlled receipts and verifies the
17-row rendering schema, canonical command policy, raw and companion artifact
hashing, semantic recomputation, secure publication, fixture non-promotion, and
the aggregate rendering-row admission shape. It intentionally does not launch
a GPU, RenderDoc, or device. Detailed operator semantics are documented in
`doc/07_guide/app/spipe/mci_v2_rendering_producer.md`.

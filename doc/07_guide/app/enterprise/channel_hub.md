# Channel Hub — generic adapter SPI and mock channel

Module: `std.enterprise_channel` (impl
`src/lib/nogc_sync_mut/enterprise_channel/channel_hub.spl`; default-tier
wrapper `src/lib/nogc_async_mut/enterprise_channel/__init__.spl`).
Lane: `.spipe/simple_enterprise_suite` W5-C. Design:
`doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md` §8.

## Mock-first rollout — Amazon is explicitly FUTURE

This module is **rollout step 1 only** (§8.3): the generic adapter SPI plus a
deterministic mock channel. No Amazon (or any provider-specific) code exists
here or in any business module — that is deliberate. Amazon SP-API, a Korean
channel, and Shopify come later as new `ChannelAdapter.kind` values behind
this same SPI, each with its own throttling/token-vault machinery (§8.2).
Business modules never see provider fields; the hub owns external IDs and
synchronization state, never internal business truth (§9.4).

## SPI contract

`ChannelAdapter` is a mode-struct composition seam (same pattern as the
outbox worker's `DispatchTarget` — never a closure stored in a struct).
Canonical operations, step-1 subset:

| Operation | Signature | Mock behavior |
|---|---|---|
| publish listing | `channel_publish_listing(adapter, sku, price) -> (ok, external_listing_id)` | deterministic `ext-listing-<sku>` |
| update quantity | `channel_update_quantity(adapter, sku, qty) -> ok` | ok unless downed |
| fetch orders | `channel_fetch_orders(adapter, cursor) -> ChannelFetch(ok, orders, next_cursor)` | pages the scripted list by numeric cursor |
| acknowledge order | `channel_acknowledge_order(adapter, external_id) -> ok` | ok unless downed |

Mock constructors: `mock_channel(orders, page_size)`,
`mock_channel_failing(orders, page_size, fail_cursor)` (provider error at an
exact page — for retry/checkpoint specs), `mock_channel_down(orders,
page_size)` (every call fails).

## Hub state (insert-only)

All tables are insert-only + derive, filtered in pure Simple (both store
backends): `channel_accounts` (latest status row wins; the kill switch is one
more insert — a killed channel denies every op with closed reason
`forbidden`), `channel_listings` (sku ↔ external listing id),
`channel_inbox` (dedup by external order id), `channel_checkpoints` (latest
cursor row wins — imports resume after restart), `channel_acks`.

## Import: at-least-once fetch, exactly-once effect

`channel_import_orders(store, session, tenant, who, envelope, adapter,
channel_id, max_batch)` runs the frozen guarded sequence (session → rbac →
domain/kill → per-order idempotency → effects). Each NEW external order
creates one internal order via `sale_place_order` with idempotency key
`chan:<channel>:<external_id>`, plus one inbox row; the checkpoint commits
after each successful page. A provider failure mid-batch leaves the cursor at
the last success; the rerun resumes there and inbox dedup (plus sale
idempotency) keeps the internal effect exactly-once. An order the sale
vertical rejects (unknown sku, no stock) is recorded in the inbox with an
empty internal order id so reconciliation flags it.

## Reconciliation

`channel_reconcile(store, tenant_id, channel_id)` returns data (never
prints): `inbox_total`, `imported_count`, `orphan_external_ids` (inbox
without internal order), `unacked_external_ids` (internal order without ack),
`checkpoints_recorded`, `last_cursor`.

## Specs

`test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl`
(9/9; red-first proven on the inbox dedup: with dedup disabled the replay
spec fails inbox 8≠4). Generated manual:
`doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.md`.
Runner: Rust seed, interpreter mode, one spec at a time,
`SIMPLE_TIMEOUT_SECONDS=900`.

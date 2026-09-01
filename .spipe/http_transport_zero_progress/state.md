# Feature: http-transport-zero-progress

## Raw Request

Harden the Simple web server so every supported protocol remains correct under real transport behavior.

## Task Type

bug

## Refined Goal

Keep non-empty HTTP transport writes pending until a positive byte transfer occurs.

## Acceptance Criteria

- AC-1: text, byte-buffer, and sendfile operations do not complete from writable readiness plus a zero-byte write result.
- AC-2: a positive byte transfer remains the sole success-progress condition and negative results preserve Worker terminal-error handling.
- AC-3: the worker retains its existing one-in-flight transport payload and short-positive retry behavior.
- AC-4: focused unit evidence covers zero, positive, and negative result classification.
- AC-5: no public HTTP behavior/API changes; docs and LLM wiki are N/A because this is an internal I/O completion invariant documented beside the shared predicate.

## Scope Exclusions

No TLS re-encryption changes, HTTP/2 scheduling redesign, WebSocket feature work, or socket-backend replacement.

## Cooperative Review

High-effort reviewer `/root/web_transport_review`; merge owner `/root`; shared interface `io_write_completion_has_progress_v1`; final reviewer pending transport/H2 interaction audit.

## Phase

impl-done-unverified-runtime

## Log

- impl: Replaced readiness-derived completion in text, byte, and sendfile operations with one positive-progress predicate.
- review: High-effort transport review accepted the one-owner retry design and required an empty-chunk sendfile terminal error; no API or parallel-send change is needed.
- impl: Added the terminal sendfile-truncation guard so a positive requested body with no available bytes cannot wait indefinitely.
- evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/io/driver_write_completion_spec.spl --mode=interpreter` passed 5/5 after the final change. The runner emitted the bootstrap-seed warning, so this is focused diagnostic evidence, not release evidence.

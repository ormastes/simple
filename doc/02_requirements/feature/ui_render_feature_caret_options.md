# Feature Requirement Options: UI Render Feature Caret

**Date:** 2026-04-03
**Status:** Selection required

## Option A: Shared `simple ui render` only

Implement one shared command:
- `simple ui render <file.ui.sdn>`

Scope:
- shared parser attachment in `app.ui`
- headless render/export outputs
- default demo asset support

Pros:
- lowest implementation risk
- fixes current `smux --render` inconsistency cleanly
- strong base for later adoption by other apps

Cons:
- `dashboard` and `llm_dashboard` still need migration later
- feature-caret structure remains mostly conceptual in phase 1

Effort:
- medium

## Option B: Shared `render` plus adapter migration for GUI-like apps

Implement shared `simple ui render` and add adapter entrypoints for:
- `dashboard`
- `llm_dashboard`
- `office`

Scope:
- shared parser/config contract
- app adapters that delegate into shared render
- common default asset and format semantics

Pros:
- removes immediate app-local drift
- gives all GUI-like apps a consistent render/export surface
- best user-facing coherence

Cons:
- touches more entrypoints
- requires compatibility decisions for non-`.ui.sdn` apps

Effort:
- medium-high

## Option C: Full MDSOC feature-caret migration

Implement shared `render`, app adapters, and a full feature-caret directory
layout deployed through layers with explicit transforms and checks.

Scope:
- everything in Option B
- render feature caret per layer
- transform modules
- layer-validation checks and migration rules

Pros:
- best long-term architecture
- strongest consistency with existing MDSOC direction
- creates a reusable pattern for future cross-cutting features

Cons:
- highest delivery cost
- largest refactor surface
- should be phased, not landed as one large patch

Effort:
- high

## Recommendation

Recommended starting point: **Option B**

Reason:
- it solves the user-visible drift now
- it keeps the architecture moving toward the MDSOC target
- it does not force a full structural migration in one step

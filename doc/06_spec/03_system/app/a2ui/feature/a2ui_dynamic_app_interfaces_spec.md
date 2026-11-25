# A2UI Dynamic App Interfaces System Manual

**Source Spec:** `test/03_system/app/a2ui/feature/a2ui_dynamic_app_interfaces_spec.spl`  
**Requirements:** `REQ-A2UI-009`, `REQ-A2UI-010`, `REQ-A2UI-011`  
**Design Doc:** `doc/05_design/a2ui_dynamic_app_interfaces.md`

## Overview

Verifies end-to-end dynamic UI composition, regional authority enforcement, draft preservation, and request-boundary hot-swap lifecycle separation across Caret Suite and shared SimpleUI infrastructure.

## Primary Scenarios

1. **Dynamic Screen Updates Preserve Drafts & Keep Code Generation Unchanged (`REQ-A2UI-010`)**
   - Register Caret's `caret.ui` interface and default-deny `caret_ui_policy`.
   - Edit `/draft/body` as owner `alice` on surface `main`.
   - Admit the read-only screen table and dynamically upgrade to the full 18-row interactive screen table while `code_generation` remains `1`.
   - Reject a composition candidate that attempts to mount `composer` under `detail` (`region_mount_denied`).

<!-- codex-research -->
# WM Text Access MCP — Feature Options

Date: 2026-06-01

## Option A: TRACE32-Only Promotion

**Description:** Promote the existing TRACE32 example MCP window tools into owned source and package them behind the current `t32_mcp_server`.

**Pros:**
- Smallest scope and highest certainty.
- Directly addresses TRACE32 MDI/text-window access.
- Reuses existing catalog, AREA, `WinPrint`, `PRinTer.FILE`, and action templates.

**Cons:**
- Does not generalize to host WM windows or other apps.
- Leaves `std.play.wm` and UI access protocol separate.
- A later generalized adapter may need to reshape the promoted APIs.

**Effort:** M, approximately 8-12 files.

## Option B: Shared Adapter Envelope Around Existing Sources

**Description:** Add a common `wm_text_access` adapter envelope and MCP/CLI/service schemas. Implement adapters for TRACE32 windows, Simple UI access snapshots, and basic `std.play.wm` top-level windows. Defer OS accessibility APIs to follow-up.

**Pros:**
- Establishes the reusable text-access model now.
- Avoids prematurely binding to UIA/AX/AT-SPI details.
- Lets TRACE32 and Simple UI use the same snapshot/query/action vocabulary.
- Keeps shell-backed WM support limited to what it can actually know: top-level windows and input.

**Cons:**
- Host app controls remain unavailable unless exposed by Simple UI or TRACE32.
- Requires careful capability/staleness metadata so callers do not over-trust window-level data.
- Still needs future platform semantic adapters for full arbitrary-app manipulation.

**Effort:** L, approximately 14-22 files.

## Option C: Full Cross-Platform Accessibility Adapters

**Description:** Build the shared adapter model and implement Windows UIA, macOS AX, Linux AT-SPI, TRACE32, Simple UI, and WM fallback adapters in one feature.

**Pros:**
- Closest to the requested end state for arbitrary host windows and UI items.
- Provides real semantic item access beyond top-level windows.
- Gives MCP one coherent surface for TRACE32, Simple apps, and native apps.

**Cons:**
- High platform risk and test matrix cost.
- Requires permissions and host-specific setup.
- Wayland/compositor behavior may block some operations.
- Easy to create hot-path regressions through repeated tree walks or shell-outs.

**Effort:** XL, approximately 35-55 files plus platform fixtures.

## Option D: MCP Facade Only

**Description:** Add MCP tools that wrap current `std.play.wm` and TRACE32 example commands without a shared internal protocol.

**Pros:**
- Fastest visible MCP result.
- Useful for manual workflows: list windows, focus, type, capture TRACE32 window text.

**Cons:**
- Duplicates query/action logic.
- Does not satisfy the "same logic" goal.
- Likely to accumulate backend-specific schemas and brittle agent behavior.

**Effort:** S-M, approximately 6-10 files.

## Recommendation

Option B is the best research-backed first step. It generalizes the TRACE32 text-window pattern without pretending raw WM automation can see arbitrary controls. It also creates a clean path to add UIA/AX/AT-SPI adapters later.


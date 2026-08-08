# WPT-derived web layout manager parity corpus

**Executable source:** `test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl`
**Requirements:** REQ-WLM-003, REQ-WLM-004, REQ-WLM-005

This bounded corpus reuses existing repository Web Platform Test and HTML
rendering witnesses. It requires the browser CPU oracle and retained layout
manager to publish exactly equal boxes, fragments, line boxes, and overflow for
full and incremental runs. The incremental receipt must name exactly the dirty
island and its dependency ancestors in document order.

## Scenario: block, Flex, and Grid

1. Run the block formatting witness derived from
   `padding_shorthand_cascade_spec.spl`.
2. Run the zero-gap Flex witness derived from
   `flex_gap_zero_cascade_spec.spl`.
3. Run the explicit-track Grid witness derived from
   `grid_foundation_wpt_spec.spl`.
4. For every witness, compare full output to the CPU oracle, compare
   incremental output to full output, and compare the exact visited-island
   receipt to the semantic ancestor closure.

## Scenario: positioned, overflow, and wrapped Latin content

1. Run the absolute-position witness derived from
   `simple_web_layout_child_index_spec.spl`.
2. Run the scrolling-overflow witness derived from
   `scrollbar_wpt_spec.spl`.
3. Run the wrapped Latin text witness derived from
   `pseudo_text_wpt_spec.spl`.
4. Apply the same exact artifact and receipt comparisons.

## Scenario: retained production session

1. Render a document containing independent Flex and Grid formatting islands.
2. Apply a scroll-only paint and require the framework epoch to remain stable.
3. Change only the Flex width while retaining the document generation.
4. Require one epoch advance and a visited receipt containing only the Flex
   island plus its dependency ancestors; the unrelated Grid island must remain
   unvisited.

## Claim boundary

This is the minimum representative corpus requested by the layout-manager
plan, not complete upstream WPT coverage. Runtime execution and canonical
docgen remain release gates; this manual does not substitute for either.

# Layout selector matcher: residual limits of the step budget (2026-11-14)

Status: OPEN. Severity: low to medium (bounded work, but the bounds are per
match and some legitimate selectors can be refused on very large pages).

Context: `simple_web_html_layout_renderer_core_selectors.spl` bounds ONE
top-level selector match (rule x node) by `SELECTOR_STEP_BUDGET` = 100,000
compound evaluations. On exhaustion the rule does not match that node and
`simple_web_selector_budget_exhausted_count()` increments. Exhaustion is
sticky and fails closed, including through `:not()` / `:is()` and at the
compound-level entries. What that does not cover:

1. **No per-document cap and no exhausted-rule memo.** The budget resets for
   every (rule, node) pair. A rule that exhausts on every node costs
   100,000 steps x node count; nothing remembers "this rule already blew the
   budget in this pass" or caps the style pass as a whole. The render-wide
   wall budget (`WEB_RENDER_BUDGET_MS`) is the only outer bound.
2. **Recursion depth is not budgeted.** The chain walkers recurse once per
   compound and nested `:has()` / `:not()` recurse per nesting level. Selector
   size is capped (`CSS_SELECTOR_PART_CAP` parts, 32 functional nesting
   levels at parse), but stack depth is not charged against the budget.
3. **`_relates_to_anchor` steps can refuse a legitimate `:has(a b)`.** For a
   descendant-led `:has()` argument each candidate walks its parent chain to
   the scope element and each hop is a budget step. On a page where the
   scope's subtree is large and deep, the first real match can lie beyond
   100,000 steps, so the rule is refused although Chrome matches it. The same
   holds for any `:has()` whose first match is far into a large subtree.
4. **`style/supports.spl` lacks the form-feed normalisation.**
   `_nth_of_offset` treats tab, LF, CR and FF as whitespace before ` of `;
   the `@supports selector()` path normalises tab, LF and CR only, so
   `selector(:nth-child(2\fof .a))` is judged differently from the matcher.
   Also: `@supports` lower-cases its condition, so `2 OF .a` is accepted where
   Chrome 159 rejects it.

Evidence and specs: `test/01_unit/browser_engine/selector_sibling_complexity_spec.spl`
(pathological chains, fail-closed rows, cache-poisoning row, size cap),
`selector_hardening_chrome_parity_spec.spl`.

Fix direction: a per-pass memo of exhausted rules plus a per-pass step total;
charge recursion depth; an ancestor test for `:has()` that does not walk
(pre-order entry/exit numbers per node); share one whitespace normaliser
between the matcher and `supports.spl`.

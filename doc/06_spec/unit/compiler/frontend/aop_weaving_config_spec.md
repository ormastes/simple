# AOP Weaving Config Spec

Source: `test/01_unit/compiler/frontend/aop_weaving_config_spec.spl`

## Scenarios

- Disabled configs contain no rules and do not weave.
- Configs built from rules are enabled only when at least one rule exists.
- Rules are categorized by advice form.
- Predicate matching covers wildcard, exact function name, attributes, and modules.
- Predicate specificity is stable for deterministic advice ordering.
- Function weaving returns no result for disabled configs or functions without matching advice.

## Reproduction

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/frontend/aop_weaving_config_spec.spl --mode=interpreter --no-cover-check
```

# `animation: spin -1s` is dropped as invalid; Chrome reads the lone negative time as the delay (2026-11-15)

Status: OPEN. Severity: low (an authored negative-delay start offset is lost;
the element does not animate at all).

## Defect

`animation_shorthand_is_valid` (`browser_engine/simple_web_html_layout_renderer_foundation.spl`)
always validates the FIRST `<time>` token of the shorthand as the duration
(`animation_time_token_is_valid(part, time_count == 1)`), so a first time that
is negative fails the whole declaration. CSS Animations 1 section 3.11: the
first time that *can* be parsed as `animation-duration` (a non-negative
`<time>`) is the duration; a negative time cannot be, so it is the delay and
the duration keeps its initial value.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, built 2026-11-14, interpreter)

```
animation_shorthand_is_valid("spin -1s")                                  # false
apply_decls(renderer_default_style(), "animation:spin -1s", 16)          # name=none delay=0 dur=0
```

Chrome 159.0.8154.6 headless shell, `d.style.animation = "spin -1s"`:
serialised `auto ease -1s 1 normal none running spin`; computed
`animation-name: spin`, `animation-duration: 0s`, `animation-delay: -1s`.

| expression | expected | actual |
|---|---|---|
| `animation_shorthand_is_valid("spin -1s")` | true | false |
| applied `animation_name` / `animation_delay_ms` | `spin` / -1000 | `none` / 0 |

`transition_shorthand_is_valid` has the same first-time-is-duration shape and
should be checked against `transition: opacity -1s`.

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_style_value_parsers_spec.spl`
asserts the Chrome-agreeing rows only (including `spin 1s -1s`, a negative
delay after a duration); the `spin -1s` row is kept out until the fix lands.

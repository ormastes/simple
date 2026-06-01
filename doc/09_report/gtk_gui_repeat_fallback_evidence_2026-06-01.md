# GTK GUI Repeat Fallback Evidence - 2026-06-01

## Summary

The repeat GUI evidence wrapper now validates the normal Simple-vs-GTK timing
gate and a lightweight fail-closed fallback probe for unavailable vector-font
rendering.

## Latest Run

Command:

```sh
scripts/check-gtk-gui-repeat-evidence.shs
```

Key output:

```text
gtk_gui_repeat_evidence_status=pass
gtk_gui_repeat_evidence_reason=repeat-evidence-verified
gtk_gui_repeat_fallback_probe_status=pass
gtk_gui_repeat_fallback_probe_reason=forced-vector-font-unavailable
gtk_gui_repeat_simple_open_us=203
gtk_gui_repeat_gtk_open_us=68904
gtk_gui_repeat_simple_frame_us=1
gtk_gui_repeat_gtk_frame_us=25
gtk_gui_repeat_simple_vector_text_checksum=212444
```

Fallback probe report:

```text
status=unavailable
reason=forced-vector-font-unavailable
vector_font_backend=unavailable
simple_vector_text_ink_pixels=0
simple_vector_text_deterministic=true
```

## Interpretation

The fallback path is intentionally unavailable and fail-closed: the probe records
zero vector-font ink pixels and a deterministic unavailable state instead of
claiming rendered output when the vector-font backend is forced off.

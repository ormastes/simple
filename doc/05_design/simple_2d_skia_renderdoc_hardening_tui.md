<!-- codex-design -->
# Rendering comparison CLI status — proposed

Status: design only. The current `renderdoc-events/v1` command remains a
graphics-event diagnostic; the final-pixel command and its statuses are planned.

```text
case=16-group-opacity
input_status=ready  frame_status=complete
reference_route=angle-vulkan  candidate_route=native-simple-vulkan
reference_output=frame42:resource17:mip0:layer0
candidate_output=frame42:resource3:mip0:layer0
pixel_domain=rgba8-srgb-straight-top-left  extent=640x480
visual_status=FAIL_VISUAL  max_channel_delta=31  changed_pixels=2440
semantic_status=PASS  source=group-opacity/card-stack
receipt=build/test-artifacts/.../comparison.sdn
reference_image=build/test-artifacts/.../reference.png
candidate_image=build/test-artifacts/.../candidate.png
diff_image=build/test-artifacts/.../diff.png
```

Print the status and reason when output selection, completion, fonts, route or
pixel conversion cannot be proven. Exit nonzero on failure, unsupported,
incomplete or blocked cases. Keep image paths and typed capture metadata stable
for the generated system manual. The v1 event diagnostic may print `PASS` only
for its own event-alignment question and must not be promoted to `visual_status`.

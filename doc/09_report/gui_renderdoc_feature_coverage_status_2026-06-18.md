# GUI RenderDoc Feature Coverage Status

- status: incomplete
- reason: missing-simple-rdoc
- widget HTML renderer dispatch: 43/43
- Electron layout manifest cases: 18
- RenderDoc goal: fail (missing-simple-rdoc)
- Simple RenderDoc: fail (missing-simple-rdoc)
- External Chrome/Vulkan RenderDoc: unavailable (capture-not-requested)

## Commands

- HTML/CSS traceability: `sh scripts/check/check-html-css-sspec-traceability.shs`
- Production GUI/web parity: `ELECTRON_BITMAP_TIMEOUT_SECS=20 sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
- Simple RenderDoc: `RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-simple`
- Original Chrome/Vulkan RenderDoc: `RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs`

## Raw Evidence
- gui_renderdoc_feature_coverage_status=incomplete
- gui_renderdoc_feature_coverage_reason=missing-simple-rdoc
- widget_kind_source=src/lib/common/ui/widget_kind.spl
- widget_kind_count=43
- widget_html_renderer_source=src/app/ui.render/html_widgets.spl
- widget_html_renderer_dispatch_count=43
- widget_html_renderer_missing=
- widget_html_renderer_extra=
- electron_layout_manifest=tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt
- electron_layout_manifest_case_count=18
- electron_layout_manifest_exact_case_count=16
- electron_layout_manifest_tracked_text_case_count=2
- electron_layout_manifest_cases=css_box_matrix,border_nested_matrix,selector_inline_box_matrix,attribute_selector_box_matrix,border_box_matrix,padding_longhand_matrix,border_side_matrix,overflow_hidden_matrix,visibility_hidden_matrix,display_contents_matrix,position_absolute_matrix,position_right_bottom_matrix,position_overlap_matrix,position_z_index_matrix,opacity_matrix,background_shorthand_matrix,text_raster_track,line_height_text_track
- html_css_traceability_status=available
- html_css_traceability_reason=run sh scripts/check/check-html-css-sspec-traceability.shs
- html_css_traceability_command=sh scripts/check/check-html-css-sspec-traceability.shs
- production_gui_web_renderer_parity_command=ELECTRON_BITMAP_TIMEOUT_SECS=20 sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
- production_gui_web_renderer_parity_existing_env=build/production_gui_web_renderer_parity_evidence/evidence.env
- production_gui_web_renderer_parity_existing_status=missing-status
- production_gui_web_renderer_parity_existing_reason=existing-evidence-env-missing-production-status
- production_gui_web_renderer_parity_existing_layout_case_count=
- production_gui_web_renderer_parity_existing_layout_pass_count=
- production_gui_web_renderer_parity_existing_layout_tracked_count=
- production_gui_web_renderer_parity_existing_layout_fail_count=
- renderdoc_goal_status_command=sh scripts/check/check-html-css-renderdoc-goal-status.shs
- renderdoc_goal_status_exit_code=1
- renderdoc_goal_status=fail
- renderdoc_goal_reason=missing-simple-rdoc
- simple_renderdoc_status=fail
- simple_renderdoc_reason=missing-simple-rdoc
- external_renderdoc_status=unavailable
- external_renderdoc_reason=capture-not-requested
- macos_portability_status=pass
- macos_portability_reason=macos-portability-recorded
- simple_renderdoc_capture_command=RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-simple
- html_renderdoc_capture_command=RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs
- blocked_completion_gate=original Chrome-on-Vulkan RenderDoc .rdc with RDOC magic

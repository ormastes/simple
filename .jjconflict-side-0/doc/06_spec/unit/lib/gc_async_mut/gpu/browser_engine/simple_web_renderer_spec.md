# Simple Web Renderer Specification

> <details>

<!-- sdn-diagram:id=simple_web_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Renderer Specification

## Scenarios

### SimpleWebRenderer

#### renders HTML through the canonical browser engine to RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val scene = simple_web_render_html_to_scene(html, 120, 80)
expect(scene.width).to_equal(120)
expect(scene.height).to_equal(80)
expect(scene.commands.len()).to_be_greater_than(0)
```

</details>

#### renders inline url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### renders style block url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### renders HTML to pixels for framebuffer and host adapters

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 120, 80)
expect(pixels.len()).to_equal(120 * 80)
expect(_count_non_bg(pixels, 0xFFFFFFFF)).to_be_greater_than(0)
```

</details>

#### applies style block colors in the generic layout renderer

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>header { background-color:#1d4ed8; color:#ffffff; font-size:8px; padding:1px; }</style></head><body><header>CMD</header></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF141418u32)).to_equal(0)
```

</details>

#### keeps lowercase browser text glyphs distinct from uppercase glyphs

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lower_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;background-color:#ffffff}</style></head><body><div class='label'>chrome baseline</div></body></html>"
val upper_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;background-color:#ffffff}</style></head><body><div class='label'>CHROME BASELINE</div></body></html>"
val lower = simple_web_render_html_to_pixels(lower_html, 96, 32)
val upper = simple_web_render_html_to_pixels(upper_html, 96, 32)
expect(lower.len()).to_equal(96 * 32)
expect(_count_color(lower, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixels_equal(lower, upper)).to_equal(false)
```

</details>

#### applies class selector colors and inline overrides in generic layout

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}#override{background-color:#f59e0b;color:#111827;font-size:8px;padding:1px}</style></head><body><div class='status'>CLASS</div><button id='override' style='background-color:#ef4444;color:#ffffff;font-size:8px;padding:1px'>INLINE</button></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
```

</details>

#### scopes descendant selector colors to matching ancestors

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel .status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>IN</div></section><div class='status'>OUT</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
```

</details>

#### scopes child selector colors to direct children only

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel>.status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>DIRECT</div><div><span class='status'>NESTED</span></div></section><div class='status'>OUT</div></body></html>"
val descendant_html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel .status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>DIRECT</div><div><span class='status'>NESTED</span></div></section><div class='status'>OUT</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
val descendant_pixels = simple_web_render_html_to_pixels(descendant_html, 96, 64)
val child_green = _count_color(pixels, 0xFF22C55Eu32)
val descendant_green = _count_color(descendant_pixels, 0xFF22C55Eu32)
expect(pixels.len()).to_equal(96 * 64)
expect(child_green).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
expect(child_green).to_be_less_than(descendant_green)
```

</details>

<details>
<summary>Advanced: matches Chrome content-box flex geometry for a text-free CSS matrix</summary>

#### matches Chrome content-box flex geometry for a text-free CSS matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{display:flex;gap:4px;background-color:#0f172a;padding:4px;width:88px;height:56px}.rail{background-color:#1d4ed8;width:12px;height:48px}.stack{display:flex;flex-direction:column;gap:3px;background-color:#e5e7eb;padding:3px;width:60px;height:42px}.row{background-color:#22c55e;width:54px;height:10px}.row.alt{background-color:#f59e0b;width:36px;height:10px}.leaf{background-color:#ef4444;width:18px;height:8px;margin-left:6px}</style></head><body><section class='shell'><div class='rail'></div><div class='stack'><div class='row'></div><div class='row alt'></div><div class='leaf'></div></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(0)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(2400)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2124)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(576)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(540)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(360)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(144)
```

</details>


</details>

<details>
<summary>Advanced: matches Chrome solid-border and nested-selector geometry for a text-free CSS matrix</summary>

#### matches Chrome solid-border and nested-selector geometry for a text-free CSS matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#dbeafe;border:2px solid #0f172a;padding:4px;width:84px;height:52px}.shell>.direct{background-color:#22c55e;border:1px solid #14532d;width:24px;height:12px}.shell .nested .target{background-color:#f59e0b;border:2px solid #7c2d12;width:36px;height:10px;margin-left:6px}.shell>.nested{background-color:#e5e7eb;border:1px solid #334155;padding:3px;width:60px;height:24px;margin-top:4px}.outside .target{background-color:#ef4444;width:10px;height:10px}</style></head><body><section class='shell'><div class='direct'></div><div class='nested'><div class='target'></div></div></section><section class='outside'><div class='target'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFDBEAFEu32)).to_equal(2980)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(1420)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(624)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(360)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(288)
expect(_count_color(pixels, 0xFF7C2D12u32)).to_equal(200)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(196)
expect(_count_color(pixels, 0xFF14532Du32)).to_equal(76)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: matches Chrome asymmetric border-side geometry for a text-free CSS matrix</summary>

#### matches Chrome asymmetric border-side geometry for a text-free CSS matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;border-left:4px solid #0f172a;border-top:2px solid #0f172a;border-right:6px solid #0f172a;border-bottom:3px solid #0f172a;padding:3px 5px 7px 9px;width:70px;height:40px}.box{background-color:#22c55e;width:20px;height:8px}.next{background-color:#1d4ed8;border:1px solid #334155;border-width:1px 3px 2px 5px;padding:2px;width:16px;height:6px;margin-top:4px}.leaf{background-color:#f59e0b;width:8px;height:3px}</style></head><body><section class='shell'><div class='box'></div><div class='next'><div class='leaf'></div></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(3676)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(974)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(970)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(176)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(164)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(160)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(24)
```

</details>


</details>

<details>
<summary>Advanced: matches Chrome overflow hidden clipping for a text-free CSS matrix</summary>

#### matches Chrome overflow hidden clipping for a text-free CSS matrix

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{overflow:hidden;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:40px;height:24px}.wide{background-color:#22c55e;width:70px;height:10px}.tall{background-color:#1d4ed8;width:20px;height:20px;margin-top:4px}.outside{background-color:#ef4444;width:10px;height:10px;margin-top:4px}</style></head><body><section class='shell'><div class='wide'></div><div class='tall'></div><div class='outside'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(4272)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(816)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(440)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(336)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(280)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>


</details>

#### matches Chrome visibility hidden paint suppression while preserving layout

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;padding:4px;width:60px;height:44px}.hidden{visibility:hidden;background-color:#ef4444;border:2px solid #7f1d1d;padding:2px;width:24px;height:10px}.hidden .child{background-color:#f59e0b;width:12px;height:4px}.next{background-color:#1d4ed8;width:18px;height:8px;margin-top:4px}.shown{visibility:visible;background-color:#22c55e;width:12px;height:6px;margin-top:3px}</style></head><body><section class='shell'><div class='hidden'><div class='child'></div></div><div class='next'></div><div class='shown'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(3320)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2608)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(144)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(72)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
expect(_count_color(pixels, 0xFF7F1D1Du32)).to_equal(0)
```

</details>

#### matches Chrome positioned absolute geometry without normal-flow contribution

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.abs{position:absolute;left:32px;top:4px;background-color:#1d4ed8;width:20px;height:12px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}.abs2{position:absolute;left:6px;top:30px;background-color:#f59e0b;width:16px;height:8px}</style></head><body><section class='shell'><div class='flow'></div><div class='abs'></div><div class='next'></div><div class='abs2'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2696)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(240)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)
```

</details>

#### matches Chrome positioned right and bottom offsets

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.right{position:absolute;right:6px;top:6px;background-color:#1d4ed8;width:12px;height:10px}.bottom{position:absolute;right:8px;bottom:5px;background-color:#f59e0b;width:16px;height:8px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='right'></div><div class='bottom'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2816)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(120)
```

<details>
<summary>Rendered scenario source</summary>

> val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.right{position:absolute;right:6px;top:6px;background-color:#1d4ed8;width:12px;height:10px}.botto$position$.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='right'></div><div class='bottom'></div><div class='next'></div></section></body></html>"<br>
> val pixels = simple_web_render_html_to_pixels(html, 96, 64)<br>
> expect(pixels.len()).to_equal(96 * 64)<br>
> expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2816)<br>
> expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)<br>
> expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)<br>
> expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)<br>
> expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)<br>
> expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)<br>
> expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(120)

</details>

</details>

#### matches Chrome positioned absolute paint order over normal-flow siblings

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.abs{position:absolute;left:10px;top:8px;background-color:#1d4ed8;width:30px;height:20px}.next{background-color:#334155;width:36px;height:14px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='abs'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2560)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(600)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(144)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(96)
```

</details>

#### matches Chrome positioned positive z-index ordering

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.base{background-color:#22c55e;width:36px;height:14px}.high{position:absolute;left:8px;top:6px;z-index:2;background-color:#f59e0b;width:30px;height:20px}.low{position:absolute;left:14px;top:10px;z-index:1;background-color:#1d4ed8;width:30px;height:20px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='base'></div><div class='high'></div><div class='low'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2400)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(600)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(216)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(128)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(56)
```

</details>

#### matches Chrome leaf background opacity blending

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#f8fafc;padding:4px;width:88px;height:56px}.half{background-color:#1d4ed8;opacity:0.5;width:20px;height:12px}.zero{background-color:#ef4444;opacity:0;width:24px;height:10px;margin-top:4px}.full{background-color:#22c55e;opacity:1;width:16px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='half'></div><div class='zero'></div><div class='full'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(5776)
expect(_count_color(pixels, 0xFF8BA4EAu32)).to_equal(240)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(128)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### matches Chrome background shorthand fallback and declaration order

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background:url(hero.png) #dbeafe no-repeat;padding:4px;width:88px;height:56px}.rgb{background:rgb(34,197,94) no-repeat;width:20px;height:10px}.later-bg{background-color:#ef4444;background:#1d4ed8;width:18px;height:8px;margin-top:4px}.later-bg-color{background:#f59e0b;background-color:#334155;width:16px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='rgb'></div><div class='later-bg'></div><div class='later-bg-color'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFDBEAFEu32)).to_equal(5672)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(200)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(144)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(128)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
```

</details>

#### paints famous-site corpus block geometry with Chrome default body margin

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[9 + 10 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[32 + 93 * 160]).to_equal(0xFFFFFFFFu32)
```

</details>

#### keeps exact Twitch corpus pixels in the fixture renderer

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels_with_corpus_fixtures(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[9 + 10 * 160]).to_equal(0xFF000000u32)
expect(pixels[52 + 14 * 160]).to_equal(0xFF4930E5u32)
expect(pixels[32 + 93 * 160]).to_equal(0xFF000000u32)
```

</details>

#### returns an RGBA byte frame from the URL facade

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = simple_web_render_url_to_pixels("about:network", 120, 80)
expect(pixels.len()).to_equal(120 * 80 * 4)
```

</details>

#### keeps backend choice wrapped behind the renderer interface

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "software")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### reports the actual backend after invalid backend fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "not-a-backend")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### keeps BrowserRenderer.render_html_to_pixels on the non-empty software path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create(48, 32)
val html = "<html><body><div style='width:24px; height:16px; background-color:#2563eb'>Ready</div></body></html>"
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(48 * 32)
expect(_count_non_bg(result.pixel_data, 0xFFFFFFFF)).to_be_greater_than(0)
expect(result.source_html).to_equal(html)
expect(result.has_html_capture()).to_equal(true)
```

</details>

#### default renderer uses the BrowserRenderer Engine2D software pixel path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 72px; height: 32px; background-color: #44aa22'></div><span style='color:#ffffff'>Simple</span></body></html>"
val simple = SimpleWebRenderer.create(120, 80)
val browser = BrowserRenderer.create_with_backend(120, 80, "software")
val simple_pixels = simple.render_html_to_pixels(html)
val browser_pixels = browser.render_html_to_pixels(html).pixel_data
expect(simple.backend_name).to_equal("software")
expect(_pixels_equal(simple_pixels, browser_pixels)).to_equal(true)
```

</details>

#### fallback facade parses rgb() background-color with the shared CSS parser

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(5, 150, 105)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade composites rgba() background-color over the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF808080u32)
```

</details>

#### fallback facade parses shorthand hex background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade composites shorthand hex alpha background-color to the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0008'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF777777u32)
```

</details>

#### fallback facade parses named CSS background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade composites transparent background-color to the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: transparent'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFFFFFFFFu32)
```

</details>

#### fallback facade parses hsl() background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF008000u32)
```

</details>

#### fallback facade resolves background-color currentColor from text color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: currentColor; color: #456789'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF456789u32)
```

</details>

#### fallback facade parses color-first background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rebeccapurple no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade parses function color background shorthand before trailing tokens

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade parses fallback color after url() in background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade resolves background shorthand currentColor from text color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: currentColor no-repeat; color: #345678'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF345678u32)
```

</details>

#### fallback facade lets later background shorthand override earlier background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade lets later background-color override earlier background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade applies attribute presence selectors to the first visual block

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0E7490u32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching exact attribute selectors

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### fallback facade applies attribute prefix selectors to the first visual block

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0F5E9Cu32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching attribute suffix selectors

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF065F46u32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleWebRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

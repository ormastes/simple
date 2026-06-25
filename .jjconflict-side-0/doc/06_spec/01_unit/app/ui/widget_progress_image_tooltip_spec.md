# Widget Progress Image Tooltip Specification

> <details>

<!-- sdn-diagram:id=widget_progress_image_tooltip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_progress_image_tooltip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_progress_image_tooltip_spec -> common
widget_progress_image_tooltip_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_progress_image_tooltip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Progress Image Tooltip Specification

## Scenarios

### Progress widget builder

#### creation

#### creates widget with kind progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_create_1", 75)
expect p.kind to_equal "progress"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_create_2", 50)
expect p.id to_equal "prog_create_2"
```

</details>

#### value property

#### stores value as string prop

1. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_val_1", 75)
expect p.get_prop("value") to_equal "75"
```

</details>

#### stores zero value

1. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_val_2", 0)
expect p.get_prop("value") to_equal "0"
```

</details>

#### stores full value

1. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_val_3", 100)
expect p.get_prop("value") to_equal "100"
```

</details>

#### stores small value

1. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_val_4", 1)
expect p.get_prop("value") to_equal "1"
```

</details>

#### children

#### has no children

1. expect p child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_child_1", 60)
expect p.child_count() to_equal 0
```

</details>

#### visibility

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_vis_1", 33)
expect p.visible to_equal true
```

</details>

#### layout

#### has default vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("prog_lay_1", 50)
expect p.layout to_equal "vbox"
```

</details>

### Progress widget HTML rendering

#### structure

#### contains widget-progress class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_html_1", 75)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-progress"
```

</details>

#### starts with div tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_html_2", 50)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<div"
```

</details>

#### contains progress-bar inner div

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_html_3", 40)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "progress-bar"
```

</details>

#### percentage display

#### contains percentage text for 75

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_pct_1", 75)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "75%"
```

</details>

#### contains percentage text for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_pct_2", 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "0%"
```

</details>

#### contains percentage text for 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_pct_3", 100)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "100%"
```

</details>

#### style width

#### contains width style for 75

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_sty_1", 75)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "width: 75%"
```

</details>

#### contains width style for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_sty_2", 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "width: 0%"
```

</details>

#### contains width style for 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_sty_3", 100)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "width: 100%"
```

</details>

#### id attribute

#### contains the widget id in the output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = progress("prog_id_1", 55)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "prog_id_1"
```

</details>

### Image widget builder

#### creation

#### creates widget with kind image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_create_1", "photo.png", "A photo")
expect img.kind to_equal "image"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_create_2", "pic.jpg", "Picture")
expect img.id to_equal "img_create_2"
```

</details>

#### src property

#### stores src prop

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_src_1", "photo.png", "A photo")
expect img.get_prop("src") to_equal "photo.png"
```

</details>

#### stores url src

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_src_2", "https://example.com/img.png", "Remote")
expect img.get_prop("src") to_equal "https://example.com/img.png"
```

</details>

#### stores empty src

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_src_3", "", "No image")
expect img.get_prop("src") to_equal ""
```

</details>

#### alt property

#### stores alt prop

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_alt_1", "photo.png", "A photo")
expect img.get_prop("alt") to_equal "A photo"
```

</details>

#### stores empty alt

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_alt_2", "pic.jpg", "")
expect img.get_prop("alt") to_equal ""
```

</details>

#### stores alt with spaces

1. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_alt_3", "logo.svg", "Company Logo Image")
expect img.get_prop("alt") to_equal "Company Logo Image"
```

</details>

#### children

#### has no children

1. expect img child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_child_1", "a.png", "alt")
expect img.child_count() to_equal 0
```

</details>

#### visibility

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_vis_1", "b.png", "alt")
expect img.visible to_equal true
```

</details>

#### has_prop

#### reports src exists

1. expect img has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_has_1", "c.png", "alt")
expect img.has_prop("src") to_equal true
```

</details>

#### reports alt exists

1. expect img has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_has_2", "d.png", "alt text")
expect img.has_prop("alt") to_equal true
```

</details>

#### reports missing prop as false

1. expect img has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("img_has_3", "e.png", "alt")
expect img.has_prop("nonexistent") to_equal false
```

</details>

### Image widget HTML rendering

#### structure

#### contains widget-image class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_html_1", "photo.png", "A photo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-image"
```

</details>

#### starts with img tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_html_2", "pic.jpg", "Picture")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<img"
```

</details>

#### is a self-closing tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_html_3", "icon.svg", "Icon")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_end_with "/>"
```

</details>

#### src attribute

#### contains src attribute with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_src_html_1", "photo.png", "Photo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "src=\"photo.png\""
```

</details>

#### contains src for url

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_src_html_2", "https://cdn.example.com/img.jpg", "Remote")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "src=\"https://cdn.example.com/img.jpg\""
```

</details>

#### contains empty src attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_src_html_3", "", "Empty src")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "src=\"\""
```

</details>

#### alt attribute

#### contains alt attribute with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_alt_html_1", "photo.png", "A photo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "alt=\"A photo\""
```

</details>

#### contains alt for multi-word text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_alt_html_2", "banner.png", "Welcome Banner Image")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "alt=\"Welcome Banner Image\""
```

</details>

#### contains empty alt attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_alt_html_3", "decorative.png", "")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "alt=\"\""
```

</details>

#### id attribute

#### contains the widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = image("img_id_html_1", "x.png", "X")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "img_id_html_1"
```

</details>

### Tooltip widget builder

#### creation

#### creates widget with kind tooltip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_create_1", "Help text", "target_btn")
expect tt.kind to_equal "tooltip"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_create_2", "Info", "some_target")
expect tt.id to_equal "tt_create_2"
```

</details>

#### content property

#### stores content prop

1. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_content_1", "Help text", "target_btn")
expect tt.get_prop("content") to_equal "Help text"
```

</details>

#### stores empty content

1. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_content_2", "", "btn")
expect tt.get_prop("content") to_equal ""
```

</details>

#### stores content with special characters

1. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_content_3", "Press Ctrl+S to save", "save_btn")
expect tt.get_prop("content") to_equal "Press Ctrl+S to save"
```

</details>

#### target property

#### stores target prop

1. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_target_1", "Help text", "target_btn")
expect tt.get_prop("target") to_equal "target_btn"
```

</details>

#### stores different target id

1. expect tt get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_target_2", "Click here", "submit_button")
expect tt.get_prop("target") to_equal "submit_button"
```

</details>

#### children

#### has no children

1. expect tt child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_child_1", "tip", "tgt")
expect tt.child_count() to_equal 0
```

</details>

#### visibility

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_vis_1", "tip", "tgt")
expect tt.visible to_equal true
```

</details>

#### has_prop

#### reports content exists

1. expect tt has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_has_1", "text", "tgt")
expect tt.has_prop("content") to_equal true
```

</details>

#### reports target exists

1. expect tt has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_has_2", "text", "tgt")
expect tt.has_prop("target") to_equal true
```

</details>

#### reports missing prop as false

1. expect tt has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_has_3", "text", "tgt")
expect tt.has_prop("label") to_equal false
```

</details>

### Tooltip widget HTML rendering

#### structure

#### contains widget-tooltip class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_html_1", "Help text", "target_btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tooltip"
```

</details>

#### starts with div tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_html_2", "Tip", "btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<div"
```

</details>

#### ends with closing div tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_html_3", "Info", "link")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_end_with "</div>"
```

</details>

#### data-target attribute

#### contains data-target attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_tgt_html_1", "Help", "target_btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-target"
```

</details>

#### contains target id value in data-target

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_tgt_html_2", "Hint", "my_button")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-target=\"my_button\""
```

</details>

#### contains different target id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_tgt_html_3", "Note", "save_icon")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-target=\"save_icon\""
```

</details>

#### content text

#### contains tooltip content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_cnt_html_1", "Help text", "btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Help text"
```

</details>

#### contains multi-word content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_cnt_html_2", "Click this button to submit", "submit_btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Click this button to submit"
```

</details>

#### renders empty content without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_cnt_html_3", "", "btn")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tooltip"
```

</details>

#### id attribute

#### contains the widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tooltip("tt_id_html_1", "Tip", "tgt")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tt_id_html_1"
```

</details>

### Progress, Image, Tooltip integration

#### as children in a container

#### progress can be a child of a column

1. expect col child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("integ_prog_1", 80)
val col = column("integ_col_1", [p])
expect col.child_count() to_equal 1
```

</details>

#### image can be a child of a column

1. expect col child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = image("integ_img_1", "pic.png", "Pic")
val col = column("integ_col_2", [img])
expect col.child_count() to_equal 1
```

</details>

#### all three widgets in one container

1. expect col child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("integ_prog_2", 50)
val img = image("integ_img_2", "logo.png", "Logo")
val tt = tooltip("integ_tt_1", "Help", "integ_prog_2")
val col = column("integ_col_3", [p, img, tt])
expect col.child_count() to_equal 3
```

</details>

#### prop isolation

#### progress and image have independent props

1. expect p get prop
2. expect img get prop
3. expect p get prop
4. expect img get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = progress("iso_prog_1", 42)
val img = image("iso_img_1", "file.png", "File")
expect p.get_prop("value") to_equal "42"
expect img.get_prop("src") to_equal "file.png"
expect p.get_prop("src") to_equal ""
expect img.get_prop("value") to_equal ""
```

</details>

#### tooltip and progress have independent props

1. expect tt get prop
2. expect p get prop
3. expect tt get prop
4. expect p get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("iso_tt_1", "Tip text", "target")
val p = progress("iso_prog_2", 99)
expect tt.get_prop("content") to_equal "Tip text"
expect p.get_prop("value") to_equal "99"
expect tt.get_prop("value") to_equal ""
expect p.get_prop("content") to_equal ""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_progress_image_tooltip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Progress widget builder
- Progress widget HTML rendering
- Image widget builder
- Image widget HTML rendering
- Tooltip widget builder
- Tooltip widget HTML rendering
- Progress, Image, Tooltip integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

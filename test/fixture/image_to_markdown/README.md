# Image-to-Markdown synthetic acceptance fixtures

These generated images are synthetic and contain no private data. They are
observation inputs, not self-oracles: expected visible strings and chart values
are listed here independently and must be checked against extraction output.

## `korean_table_multi_chart.png`

- SHA-256: `a362cc2651d506f44f386ecaf483df670de10cb3f37f697e1dd670679a6dd162`
- Size: 1024 × 1536 PNG
- Table headers: `항목`, `수량`, `상태`
- Highlighted row: `배 | 08 | 확인`
- Handwriting: `수량 확인`
- Panel A: `높이`, x `[0,1,2,3]`, visible y lexemes
  `[1.00,2.50,?,4.00]`, unit `mm`
- Panel B cell distribution: bins `[0-10,10-20,20-30]`, heights `[2,5,3]`
- Shared legend: `측정값`

## `rotated_cjk_log_chart.png`

- SHA-256: `7e0c7aeef222d8f9658e85d3c7c95b86589eec9972d09d759e9b196ed070d351`
- Size: 1024 × 1536 PNG
- Deliberately rotated and low contrast
- Printed text: `混合データ / 混合数据`, `English 01.00`, `日本語テスト`,
  `简体中文`, `繁體中文`
- Handwriting: `要確認`, `待确认`
- Single log chart: `成長率`, x `[1,10,100]`, visible y lexemes
  `[0.10,1.00,10.00]`
- Missing legend and an arrow overlapping the last point are deliberate.

Generated with the built-in image generation tool on 2026-09-08. Human visual
inspection confirmed the listed content before the files were admitted here.

## `multilingual_lab_form_diagram.png`

- SHA-256: `eaa118eff79fa79d340a2abd1745da92f13246f9367f01de1067f903bfaf29f2`
- Size: 1086 × 1448 PNG
- Printed headings: `실험 기록`, `試料 분석`, `실험 절차도`
- Flowchart: `입력 → 필터 → 측정 → 판정`
- Handwritten equation: `y = 2.50x² + 0.75`
- Handwritten Korean note explains x concentration (`mg/L`) and y absorbance
  (`AU`); the bottom note records refrigerated storage and no abnormality.
- Highlighted form values: `A-017`, `23.5 °C`, `101.3 kPa`, `검토 완료`
- Checkbox state: `승인` checked; `보류` and `要再確認` unchecked
- Red Japanese approval stamp: `検済`
- Photo panel caption: `Figure 1. 세포 경계`, with a visible `50 μm` scale bar

Generated with the built-in image generation tool on 2026-09-09. Human visual
inspection confirmed the listed content before admission. The fixture expands
REQ-005/006 coverage for flowchart, equation, form, checkbox, stamp/seal,
highlight, handwriting, photo, caption, and mixed-page categories.

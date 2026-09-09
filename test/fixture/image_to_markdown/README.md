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

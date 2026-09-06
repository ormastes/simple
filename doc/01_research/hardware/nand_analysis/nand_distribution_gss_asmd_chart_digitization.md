# NAND Distribution Analysis, Gaussian Structure Spectrum, and Chart Digitization

## Research, architecture, and implementation plan for the Simple language

**Status:** proposed design and implementation plan  
**Date:** 2026-09-03  
**Repository baseline:** `ormastes/simple` `main` at `a5fc77d2c4e33c0b1252cca50d3f9aab8b1b847b`  
**Primary implementation language:** Simple  
**Optional providers:** SFFI only where a native Simple implementation is not initially practical, such as OCR, a learned chart segmentor, or a GPU vendor library

## Contents

- [Decision, terminology, and research](#1-executive-decision)
- [Canonical data, inputs, and noise policy](#6-canonical-data-model)
- [GSS: FFT-like Gaussian Structure Spectrum](#9-gss--gaussian-structure-spectrum)
- [ASMD: structured overlapping-mixture inference](#10-asmd--adaptive-structured-mixture-decomposition)
- [Multiscale significance and NAND profile](#11-sizer-like-multiscale-significance)
- [Image graph-to-numeric digitization](#13-image-graph-to-numeric-digitizer)
- [LLM, plots, storage, and search](#14-image-graph-to-text-and-llm-oriented-output)
- [Simple package, APIs, and CLI](#17-simple-package-and-ownership-design)
- [Verification and implementation phases](#24-verification-and-test-strategy)
- [Acceptance, risks, pseudocode, and references](#27-acceptance-criteria)

---

## 1. Executive decision

Implement one user-facing analysis system with four internally cooperating stages:

1. **Chart/Numeric Ingest** converts CSV, XLSX/ODS, raw arrays, histograms, and raster chart images into one exact `NumericDataset` representation. Image input is digitized into numeric series before statistical analysis.
2. **GSS — Gaussian Structure Spectrum** produces an FFT-like, position-aware template-match spectrum over candidate group quantities, deviation widths, spacing, and optional shape families. Its peaks are candidate evidence, not final proportions.
3. **ASMD — Adaptive Structured Mixture Decomposition** jointly fits simultaneous, overlapping structured groups, with default group quantities `[1, 2, 4, 16]`, plus an explicit unknown residual component. It returns group portions, child parameters, uncertainty, and identifiability.
4. **Independent verification** combines SiZer-like scale-space significance, a flexible Bayesian challenge mixture, parametric-bootstrap model tests, and posterior-predictive checks. It may return `ambiguous` or `unresolved`; it must never force a 1/2/4/16 interpretation when the observations do not support one.

The recommended top-level flow is:

```text
CSV / XLSX / ODS / image / raw samples / histogram
                      │
                      ▼
              NumericDataset v1
                      │
          ┌───────────┴───────────┐
          ▼                       ▼
  scale-space significance    GSS template bank
          │                       │
          └───────────┬───────────┘
                      ▼
        exhaustive structured-model fitting
           ASMD known groups + unknown U
                      │
          ┌───────────┴───────────┐
          ▼                       ▼
  flexible challenge model   bootstrap + PPC
          └───────────┬───────────┘
                      ▼
       numeric result + SVG/PNG + LLM text
```

This design deliberately does **not** make speed the selection criterion. The CPU reference path should favor correctness, determinism, traceability, and independent verification. GPU and FFT acceleration remain provider options and must be checked against the same reference oracles.

---

## 2. Terminology and a required disambiguation

The phrase “1, 2, 4, 16 groups” can refer to different physical or statistical quantities. The implementation must encode them separately.

| Name | Meaning | Examples |
|---|---|---|
| `nand_state_count` | Number of physical threshold-voltage states for a NAND cell type | SLC 2, MLC 4, TLC 8, QLC 16 |
| `group_quantity` | Number of child lobes expected in one structured analysis group | default candidates 1, 2, 4, 16 |
| `component_count` | Number of mathematical atoms in the final fitted density | may be 23 for simultaneous 1+2+4+16 |
| `series_count` | Number of colored/independent curves in the input chart or table | 1, 2, ... |
| `dataset_count` | Number of related measurements jointly analyzed | P/E-cycle, retention-time, layer, temperature sweeps |
| `sigma` | Standard deviation of an atom or group-child distribution | voltage units or normalized x units |

For an `n`-bit NAND cell, the physical state count is

\[
S_{\mathrm{NAND}}=2^n,
\]

and there are normally

\[
S_{\mathrm{NAND}}-1
\]

read boundaries. This yields SLC/MLC/TLC/QLC state counts 2/4/8/16. The analysis default `[1,2,4,16]` is therefore **not** hard-coded as a replacement for NAND state count. In particular, TLC’s eight states must remain fully supported.

The API must use explicit field names rather than a generic `groups` integer:

```simple
class NandProfile:
    bits_per_cell: i32
    state_count: i32
    state_labels: [text]

class StructuredSearchConfig:
    group_quantities: [i32]       # default [1, 2, 4, 16]
```

---

## 3. Research conclusions

### 3.1 NAND threshold-voltage distributions

Public measurement work by Cai et al. established a read-retry-based method for building voltage histograms and reported that same-state threshold-voltage distributions can be approximated reasonably by Gaussian distributions, while a Beta distribution may fit better on average. The paper also reported P/E-cycle-dependent rightward shift and widening, and an additive-white-Gaussian-noise interpretation under ideal wear leveling. Later NAND-channel work has used Gaussian, Normal-Laplace, Student-t, nonparametric, and learned models to account for skew, long tails, cycling, retention, and process variation.

Therefore:

- Gaussian atoms are the required baseline, not the only permitted family.
- Mean shift and width growth must be first-class outputs.
- Tail-model comparison must be available before a heavy tail is misreported as an extra physical group.
- Related curves across P/E cycle, retention time, layer, and temperature should optionally be fitted jointly.
- Raw histograms and read-retry counts must remain immutable; smoothing may generate candidates but must not silently replace observations used for likelihood calculations.

### 3.2 Small bump versus real subgroup

A local maximum alone is not reliable evidence. A feature may be:

- an isolated sample fluctuation;
- text/grid contamination introduced during image digitization;
- a tail mismatch from using Gaussian atoms;
- a child of a larger coherent group;
- a real independent group;
- mathematically non-identifiable because another template is nearly collinear with it.

The selected evidence stack is:

1. significance across position and scale, using a SiZer-like derivative map;
2. coherent template response in GSS;
3. unique likelihood improvement after competing groups are jointly fitted;
4. stability across bootstrap resamples;
5. agreement or explicit disagreement with an independently flexible mixture;
6. posterior-predictive residual checks;
7. template-coherence and parameter-uncertainty diagnostics.

### 3.3 Why GSS is only analogous to FFT

An FFT uses a fixed orthogonal sinusoidal basis. Gaussian and structured NAND templates are shifted, scaled, overlapping, and generally nonorthogonal. Consequently:

- GSS does not have a unique linear inverse like an FFT.
- Neighboring GSS bins are intentionally correlated.
- A 16-child group can create responses in 1-, 2-, and 4-child templates.
- Spectrum peak height is not the estimated physical portion.
- Reconstruction and portions must come from a joint constrained fit in ASMD.

GSS remains useful because it gives a stable, inspectable “high peak means high template compatibility” representation that can be plotted and summarized for an LLM.

### 3.4 Chart image digitization

Recent chart-extraction research continues to separate three coupled tasks:

1. curve topology/tracing;
2. legend-to-curve association;
3. axis-aware mapping from pixels to numeric values.

Thin intersections, dashed lines, arbitrary legend placement, nonuniform axes, text, grid lines, antialiasing, and raster/PDF artifacts remain central failure modes. The implementation should therefore expose intermediate masks, paths, calibration, and confidence rather than return only a final table.

The recommended design is hybrid:

- deterministic geometry/color algorithms are the auditable reference path;
- OCR and learned segmentation are provider interfaces;
- manual calibration and correction are first-class, reproducible inputs;
- every digitized chart must support render-back overlay validation.

### 3.5 Repository audit

The current repository already contains useful building blocks:

| Existing capability | Current path | Reuse decision |
|---|---|---|
| NAND Vt program/erase/drift/sense and deterministic pseudo-Gaussian noise | `src/lib/hardware/nand_emu/physics.spl` | Reuse for synthetic NAND fixtures and emulator integration |
| Descriptive statistics including variance, standard deviation, skew, kurtosis, covariance, and correlation | `src/lib/common/math/statistics.spl` | Reuse; add numerically stable streaming variants rather than duplicate API |
| BLAS/LAPACK/linalg/NDArray/CUDA-provider foundations | `src/lib/common/science_math/` | Reuse as numeric backend boundary |
| FFT/rFFT/iFFT bindings through the tensor runtime | `src/compiler_rust/runtime/src/value/torch/fft.rs` | Optional accelerated GSS correlation backend; add a pure-Simple reference |
| CSV, ODS, and XLSX sheet loading | `src/app/office/sheets/sheet_io.spl` and office codecs | Reuse through a narrow tabular adapter; do not create another XLSX parser |
| Bounded pure-Simple PNG decode to ARGB | `src/lib/common/image/png_decode.spl` | Reuse |
| ARGB file/bytes image ingest | `src/lib/common/imaging/png_ingest.spl` | Reuse and generalize through a chart-image adapter |
| Basic sheet-to-SVG charts | `src/app/office/sheets/chart.spl` | Reuse SVG helpers or extract a common plotting layer for GSS/reconstruction plots |

The audit did not find a production Gaussian-mixture, NNLS, variable-projection, chart-axis/OCR, or multi-curve digitization implementation. That absence should be rechecked immediately before coding because the repository is changing rapidly.

### 3.6 Algorithm selection matrix

| Method | Noise/bump evidence | Severe overlap | Uses known 1/2/4/16 structure | Equal parent portions | Unexpected structure | Final role |
|---|---:|---:|---:|---:|---:|---|
| Local peak finder | Poor | Poor | No | No | Poor | Debug/visual aid only |
| Smoothing + peaks | Medium, bandwidth-sensitive | Poor | No | No | Poor | Never final |
| Plain GMM/EM | Medium | Medium | No | Indirect | Good | Development baseline/challenge seed |
| CWT/DoG/SiZer | **Excellent multiscale evidence** | Medium | Indirect | No | Good feature discovery | Independent significance stage |
| Gaussian sparse dictionary | Good | Good | Width dictionary only | Indirect | Good | Candidate generator |
| **GSS** | Good coherent template evidence | Very good | **Yes** | Candidate evidence only | Unknown peaks visible | FFT-like spectrum and initializer |
| **ASMD** | Through likelihood/uncertainty | **Excellent** | **Native** | **Direct constraint/test** | Explicit unknown mass | Primary estimator |
| Bayesian non-local/repulsive mixture | Good | Very good | No by design | Indirect | **Excellent** | Independent falsification/challenge model |
| Bootstrap + PPC | **Calibrates decisions** | Verifies, cannot create information | Tests any stated model | **Direct test** | Detects mismatch | Final evidence and failure gate |
| **Selected combination** | **Best available coverage** | **Best available coverage** | **Yes** | **Yes** | **Yes** | SiZer + GSS + ASMD + challenge mixture + bootstrap/PPC |

GSS and ASMD are the new project-defined algorithms that cover the gap between multiscale bump evidence and physically interpretable overlapping parent portions. The independent flexible mixture is intentionally retained so that the new structured model can be contradicted.

---

## 4. Scope

### 4.1 Required capabilities

The completed tool shall:

- load one or more numeric series from arrays, CSV, TSV, XLSX, ODS, SDN, and chart images;
- accept raw samples, binned counts, probability densities, cumulative counts, and repeated measurement series;
- preserve the original input and record every transformation;
- support no denoising, analysis-only smoothing, and explicitly requested denoising;
- generate a GSS spectrum with a configurable template bank and nine default variations;
- jointly fit simultaneous overlapping 1/2/4/16 structured groups with arbitrary nonnegative portions;
- directly test equal portions such as `portion(2) = portion(4) = portion(16)`;
- include an `unknown` structured residual so known groups are not distorted to absorb unexpected data;
- support Gaussian and at least one tail-robust atom family;
- provide a NAND profile with SLC/MLC/TLC/QLC state handling and Vt-specific metrics;
- digitize colored, solid, dotted, and dashed chart curves into numeric lists;
- reject or mark text, axes, grid lines, legend samples, and unrelated straight lines;
- produce numeric tables, an FFT-like GSS graph, reconstruction/residual graphs, an extraction overlay, and deterministic LLM-oriented text;
- attach confidence and provenance to every inferred result;
- provide a pure-Simple reference implementation and differential tests for optional accelerated providers.

### 4.2 Explicit non-goals for the first production release

- Treating a raster image as more authoritative than an available CSV/XLSX source.
- Claiming exact recovery where templates are non-identifiable.
- Replacing the NAND emulator’s physical model with the analysis model.
- Building a general-purpose OCR engine entirely inside the first chart-analysis milestone.
- Building a new spreadsheet engine or XLSX codec.
- Using an opaque learned embedding as the only stored representation.
- Making GPU availability necessary for correctness.

---

## 5. Quality modes

Performance is not the algorithm-selection priority, but the system still needs explicit semantic modes so users understand what was run.

| Mode | Meaning | Required steps |
|---|---|---|
| `explore` | Candidate visualization, not a final scientific claim | raw summary, scale space, GSS, preliminary ASMD |
| `standard` | Default supported analysis | all known masks, rigid/semi-rigid templates, unknown residual, multistart fitting, residual checks |
| `confidence` | Statistically calibrated result | `standard` + adaptive parametric bootstrap + confidence intervals + challenge mixture |
| `reference` | Best available analysis without speed constraint | all template flexibility/families, global/multistart search, high-count bootstrap, Bayesian evidence/posterior sampling, posterior-predictive checks, sensitivity analysis |

The default for research decisions should be `confidence`; the requested “best without speed consideration” behavior is `reference`.

---

## 6. Canonical data model

### 6.1 Numeric series

```simple
class AxisSpec:
    name: text
    unit: text
    scale: AxisScale
    minimum: f64
    maximum: f64

class PointUncertainty:
    x_sigma: f64
    y_sigma: f64
    confidence: f64

class NumericSeries:
    id: text
    label: text
    x: [f64]
    y: [f64]
    uncertainty: [PointUncertainty]
    color_argb: u32
    line_style: LineStyle
    source_kind: SeriesSourceKind

class NumericDataset:
    id: text
    x_axis: AxisSpec
    y_axis: AxisSpec
    series: [NumericSeries]
    observation_kind: ObservationKind
    provenance: Provenance
```

Required invariants:

- `x.len() == y.len()` for every series;
- x values are finite and either monotonic or accompanied by an explicit ordering policy;
- missing values are represented explicitly, never converted silently to zero;
- histogram bins retain edges as well as centers where available;
- counts remain counts rather than being normalized destructively;
- source units and axis transforms are retained.

### 6.2 Histogram representation

A bin-integrated likelihood is more accurate than evaluating a density only at the bin center. Represent:

```simple
class HistogramSeries:
    left_edges: [f64]
    right_edges: [f64]
    counts: [f64]
    exposure: f64
```

For component density `f`, predicted mass in bin `i` is

\[
P_i(\theta)=\int_{e_i}^{e_{i+1}} f(x;\theta)\,dx.
\]

For count data:

\[
Y_i\sim\operatorname{Poisson}(\lambda_i),\qquad
\lambda_i=N\sum_k \pi_k P_i(\theta_k)+b_i.
\]

### 6.3 Provenance

Every result must contain:

```simple
class Provenance:
    source_uri: text
    source_sha256: text
    source_sheet: text
    source_range: text
    image_region: PixelRect?
    calibration_id: text
    ingest_version: text
    analysis_version: text
    config_sha256: text
```

No result is considered reproducible without a source hash and normalized configuration hash.

---

## 7. Input adapters

### 7.1 CSV/TSV

Supported layouts:

1. **Two columns:** `x,y`.
2. **Wide multi-series:** `x,y1,y2,...`.
3. **Long form:** `series,x,y[,sigma]`.
4. **Histogram:** `left,right,count` or `center,count` with an inferred regular width.
5. **Raw samples:** one sample per row, optionally with state/condition labels.

Column selection must be explicit or confirmed through a deterministic inference report:

```text
inferred:
  x = column "Vt"
  y = column "count"
  observation_kind = histogram_count
confidence = 0.96
```

Ambiguous headers must fail with candidate mappings rather than choose arbitrarily.

### 7.2 Excel/ODS

Reuse the existing office sheet loader. Add a narrow adapter that converts selected ranges into `NumericSeries` without taking ownership of workbook parsing.

Proposed API:

```simple
fn dataset_from_sheet(
    sheet: Sheet,
    x_range: text,
    y_ranges: [text],
    label_cells: [text],
    cfg: SheetIngestConfig
) -> Result<NumericDataset, AnalysisError>
```

Features:

- sheet name/index;
- named range and A1 range support;
- header and unit extraction;
- formula cells use evaluated/cached numeric values and record that fact;
- hidden rows/columns have an explicit include policy;
- merged headers are resolved deterministically;
- chart source ranges may be read directly when an XLSX chart relationship is available in a later phase.

### 7.3 Image

Image input first produces a `DigitizedChart`, then converts to `NumericDataset`. Statistical analysis never reads pixels directly.

```simple
class DigitizedChart:
    image: ImageRef
    plot_region: PixelRect
    x_calibration: AxisCalibration
    y_calibration: AxisCalibration
    series: [DigitizedSeries]
    text_regions: [TextRegion]
    ignored_regions: [IgnoredRegion]
    validation: DigitizationValidation
```

The source image and a correction manifest remain immutable.

---

## 8. Preprocessing and noise policy

### 8.1 Three separate policies

```simple
enum PreprocessMode:
    Raw
    AnalysisOnly
    Denoise

enum DenoiseScope:
    DisplayOnly
    CandidateDetection
    Fitting
```

- `Raw`: no transformed values are created except unit conversion explicitly requested by the user.
- `AnalysisOnly`: scale-space/smoothing copies may locate candidates, but all likelihood and final fitting use raw observations.
- `Denoise`: an explicit algorithm and parameters are applied; both original and transformed data are retained. Fitting against denoised values requires an explicit `DenoiseScope.Fitting` opt-in and is never the default.

### 8.2 Observation/noise models

```simple
enum NoiseModelKind:
    Auto
    GaussianHomoscedastic
    GaussianHeteroscedastic
    Poisson
    PoissonGaussian
    StudentResidual
    EmpiricalReplicate
```

Examples:

\[
Y_i=f(x_i)+\epsilon_i,\qquad \epsilon_i\sim N(0,\tau_i^2)
\]

or

\[
Y_i\sim\operatorname{Poisson}(\lambda_i).
\]

For repeated measurements, estimate variance from replicates. Without replicates, the tool must expose assumptions and sensitivity to the chosen noise model.

### 8.3 Baseline

The baseline is a separate model, not a wide Gaussian used as a substitute:

\[
y(x)=b(x)+s(x)+\epsilon(x).
\]

Supported baselines:

- constant;
- affine;
- low-order polynomial;
- nonnegative cubic spline with smoothness penalty;
- asymmetric least-squares baseline;
- none.

The baseline choice participates in model comparison and is reported.

---

## 9. GSS — Gaussian Structure Spectrum

### 9.1 Purpose

GSS is a project-defined transform that maps a graph into a structured template-response tensor:

\[
\mathcal{S}[q,v,\mu],
\]

where:

- `q` is group quantity, default `1,2,4,16`;
- `v` is a template variation;
- `mu` is location/translation;
- each variation carries width, spacing, child-weight, and atom-family parameters.

A high GSS peak means “this local structure resembles this template under the stated noise metric.” It does not by itself mean that the corresponding group exists in the final joint model.

### 9.2 Structured template

For group quantity `q`:

\[
T_{q,v}(x;\mu)=
\sum_{j=1}^{q}w_{qvj}
 f_v\!\left(x;\mu+d_v r_{qj}+\delta_{qvj},\sigma_{qvj},\gamma_{qvj}\right),
\]

with

\[
w_{qvj}\ge 0,\qquad \sum_j w_{qvj}=1.
\]

`r_q` is the canonical relative child layout; `d_v` is spacing; `delta` permits controlled distortion; `f_v` is Gaussian by default.

### 9.3 Whitened matched response

Let residual `r = y - b - M_current` and let `W` be the inverse noise covariance or diagonal inverse variance. For template vector `t`:

\[
\hat a(\theta)=
\max\left(0,
\frac{t^TWr}{t^TWt}
\right).
\]

The normalized match score is

\[
Z(\theta)=
\frac{t^TWr}{\sqrt{t^TWt}}.
\]

For a Gaussian residual model with correctly whitened observations, the one-template generalized likelihood-ratio improvement is

\[
2\Delta\ell(\theta)=
\frac{\max(0,t^TWr)^2}{t^TWt}.
\]

For Poisson counts, optimize the one-dimensional nonnegative amplitude against bin-integrated predicted counts and report Poisson deviance improvement instead.

### 9.4 Raw and unique spectra

Store both:

\[
S_{\mathrm{raw}}(q,v)=\max_\mu Z(q,v,\mu)
\]

and

\[
S_{\mathrm{unique}}(q,v)=
2\left[\ell(M+\hat\alpha T_{qv})-\ell(M)\right],
\]

where `M` contains already selected competing groups. `S_unique` helps distinguish a template that merely correlates with a larger group from one that adds unique explanatory structure.

### 9.5 Default nine variations

The invariant is **nine distinct default templates per quantity**, with a configurable bank.

For `q > 1`, default to three width factors by three spacing factors:

```text
width_factor   = [0.80, 1.00, 1.25]
spacing_factor = [0.80, 1.00, 1.25]
```

| Variation | Width | Spacing |
|---:|---:|---:|
| 1 | 0.80 | 0.80 |
| 2 | 0.80 | 1.00 |
| 3 | 0.80 | 1.25 |
| 4 | 1.00 | 0.80 |
| 5 | 1.00 | 1.00 |
| 6 | 1.00 | 1.25 |
| 7 | 1.25 | 0.80 |
| 8 | 1.25 | 1.00 |
| 9 | 1.25 | 1.25 |

For `q == 1`, spacing is undefined. Do not create six duplicate templates. The default bank instead uses nine log-symmetric width factors around the nominal width:

```text
[0.50, 0.63, 0.80, 0.90, 1.00, 1.11, 1.25, 1.59, 2.00]
```

Alternative `q == 1` banks may use `3 width × 3 atom-shape` variations when heavy-tail/skew analysis is enabled.

The user may replace either bank with arbitrary discrete templates or a continuous optimization range.

#### Nominal width and spacing precedence

The factors above multiply nominal values `sigma0` and `d0`. Their provenance is explicit. Use this precedence:

1. user-specified physical values;
2. NAND/product/profile calibration;
3. values learned from a jointly fitted reference dataset;
4. robust scale-space and pair-spacing estimates from the current raw graph;
5. a clearly labeled normalized exploratory fallback based on x range.

A generic fallback must never be presented as a NAND physical constant. In `reference` mode the bank is an initializer: after discrete peaks are found, center, width, and spacing are continuously refined and profile/evidence sensitivity to the starting bank is reported.

```simple
class NominalTemplateScale:
    sigma0: f64
    spacing0: f64
    source: NominalScaleSource
    confidence: f64
```

### 9.6 Position-aware output

Retain the full tensor when practical:

```text
score[quantity][variation][position]
```

Derive:

- a flattened FFT-like spectrum over `(quantity, variation)`;
- a quantity summary `max_{v,mu}`;
- a width/spacing heatmap;
- a position-versus-template spectrogram;
- clustered peak candidates.

Neighboring high bins are clustered as one candidate in continuous parameter space; they are not counted as separate groups.

### 9.7 GSS plot

The primary plot has four panels or four clearly marked bands:

```text
match / unique evidence
^
|        q=1       q=2       q=4                     q=16
|        1..9      1..9      1..9                    1..9
+----------------------------------------------------------------> template id
```

Each plotted point carries machine-readable metadata:

```text
quantity=16
variation=6
width_factor=1.00
spacing_factor=1.25
best_center=8.27
raw_match=0.93
unique_llr=68.1
amplitude_seed=0.29
```

The SVG should embed these values as element attributes or a sibling SDN/JSON data block so an LLM or test does not have to recover them from pixels.

### 9.8 GSS pseudocode

```simple
fn gss_transform(
    data: NumericSeries,
    bank: GssTemplateBank,
    noise: NoiseModel,
    baseline: BaselineModel
) -> Result<GssSpectrum, AnalysisError>:
    val residual = noise.whiten(data.y - baseline.predict(data.x))
    var cells: [GssCell] = []

    for family in bank.families:
        for variation in family.variations:
            val template = build_template(family.quantity, variation, data.x)
            val position_scores = correlate_all_positions(residual, template, noise)
            val peak = position_scores.maximum()
            cells.push(GssCell(
                quantity: family.quantity,
                variation_id: variation.id,
                best_position: peak.position,
                raw_match: peak.z,
                raw_llr: peak.llr,
                position_scores: position_scores.values
            ))

    Ok(cluster_gss_peaks(GssSpectrum(cells: cells)))
```

`correlate_all_positions` has a direct reference implementation and optional FFT/GPU providers. Both return numerically comparable cells.

---
## 10. ASMD — Adaptive Structured Mixture Decomposition

### 10.1 Purpose

ASMD is the final physical/statistical estimator. It jointly explains the observed curve using known structured groups and an unknown component:

\[
\boxed{
p(x)=b(x)+
\sum_{q\in Q}\alpha_q H_q(x;\theta_q)
+\alpha_U U(x;\psi)
}
\]

where

\[
Q=\{1,2,4,16\}\quad\text{by default},
\]

\[
\alpha_q\ge0,\quad \alpha_U\ge0,
\]

and, for normalized densities,

\[
\sum_q\alpha_q+\alpha_U=1.
\]

Each `H_q` is itself a normalized child mixture:

\[
H_q(x;\theta_q)=
\sum_{j=1}^{q} w_{qj}
 f(x;\mu_{qj},\sigma_{qj},\gamma_{qj}),
\quad
\sum_jw_{qj}=1.
\]

The directly reported parent portion is `alpha_q`. It is not inferred from the height of one child. This is critical when groups 2, 4, and 16 have equal total portions: an equal-child 16 group assigns only `alpha_16/16` to each child and may show small or invisible local peaks despite strong joint evidence.

### 10.2 Known and unknown mass

The unknown component prevents model coercion:

\[
U(x;\psi)=
\sum_{k=1}^{K_U}\beta_k u(x;\nu_k,\tau_k,\xi_k),
\quad \sum_k\beta_k=1.
\]

It may be implemented as:

- a small unconstrained Gaussian/Student mixture;
- a positive spline density;
- a nonparametric kernel component;
- a domain-specific nuisance family.

The output explicitly separates:

```text
known_structured_mass = alpha_1 + alpha_2 + alpha_4 + alpha_16
unknown_structured_mass = alpha_U
```

A substantial `alpha_U` is a model-mismatch result, not a failed optimization to hide.

### 10.3 Atom families

```simple
enum AtomFamilyKind:
    Gaussian
    NormalLaplace
    StudentT
    SkewNormal
    BetaWindowed
    PositiveSpline
```

Recommended order:

1. Gaussian baseline;
2. Student-t or Normal-Laplace tail challenge;
3. skew-normal when residuals show one-sided shape;
4. Beta only for bounded/normalized support with justified boundaries;
5. positive spline for the unknown residual.

The fitter must compare whole model families. It must not add multiple Gaussian components merely to approximate one heavy-tailed state without flagging that interpretation.

### 10.4 Structural levels

For each quantity `q`, fit increasingly flexible models.

#### Rigid

\[
\mu_{qj}=c_q+d_q r_{qj},
\]

\[
\sigma_{qj}=\sigma_q,
\]

\[
w_{qj}=1/q.
\]

This gives approximately four primary parameters per group: total portion, center, spacing, and width.

#### Semi-rigid

\[
\mu_{qj}=c_q+d_qr_{qj}+\delta_{qj},
\]

\[
\sigma_{qj}=\sigma_q e^{\eta_{qj}},
\]

\[
w_{qj}=\frac{e^{z_{qj}}}{\sum_r e^{z_{qr}}}.
\]

Regularization:

\[
R_q=
\lambda_\mu\sum_j\delta_{qj}^2+
\lambda_\sigma\sum_j\eta_{qj}^2+
\lambda_w\sum_j\left(w_{qj}-\frac1q\right)^2+
\lambda_{\Delta}\sum_j(\delta_{q,j+1}-\delta_{qj})^2.
\]

#### Flexible

Child centers, widths, and weights are free subject to ordering, minimum separation, positive width, and prior/penalty constraints. This level is used only when its predictive evidence justifies the additional freedom.

### 10.5 Exhaustive parent-presence search

With four default known quantities, there are only

\[
2^4=16
\]

presence masks, including the empty known model. Fit all masks:

```text
{}
{1} {2} {4} {16}
{1,2} {1,4} ...
{1,2,4} ...
{1,2,4,16}
```

For each mask, evaluate rigid, semi-rigid, and justified flexible variants, with and without the unknown component. Do not use greedy peak counting as the primary model selector.

If users configure more quantities, use branch-and-bound or reversible-jump/SMC exploration but retain exhaustive enumeration when the model space is small.

### 10.6 Variable projection

For fixed nonlinear shape parameters `theta`, construct the design matrix

\[
\Phi(\theta)=
[H_{q_1},H_{q_2},\ldots,H_{q_m},U_1,\ldots].
\]

The portions/amplitudes are linear or conditionally convex:

\[
\alpha^*(\theta)=
\arg\min_{\alpha\ge0}
\|W^{1/2}(y-b-\Phi(\theta)\alpha)\|_2^2.
\]

Then solve only the reduced nonlinear problem:

\[
\theta^*=\arg\min_\theta
L\bigl(\theta,\alpha^*(\theta)\bigr)+R(\theta).
\]

For normalized density data, add `sum(alpha) = 1`. For Poisson histograms, solve the nonnegative convex amplitude subproblem under the Poisson log-likelihood rather than ordinary NNLS.

Required numerical methods:

- active-set or block-pivoting NNLS reference;
- equality-constrained simplex projection;
- trust-region reflective nonlinear optimization;
- automatic or verified analytic Jacobians;
- multistart/global seeding from GSS and scale-space ridges;
- parameter transforms (`log sigma`, softmax weights) to enforce constraints.

### 10.7 Global and multistart fitting

Mixtures have local optima and label symmetry. The `reference` mode shall:

1. seed every active group from several GSS peak clusters;
2. seed group portions from constrained linear solves;
3. include random-but-deterministic Latin-hypercube/Sobol starts;
4. fit each start to convergence;
5. canonicalize labels by parent quantity, then parent center, then child center;
6. retain all distinct local solutions within a configurable likelihood/evidence window;
7. report multimodal parameter uncertainty rather than averaging incompatible solutions.

A deterministic seed is recorded in provenance.

### 10.8 Model evidence and challenge model

No single information criterion should be the final judge. Use a staged but non-speed-prioritized decision:

1. predictive log likelihood or held-out deviance;
2. MDL/BIC/singular-BIC as summaries, not sole authority;
3. Bayesian evidence/posterior model probabilities for finalists;
4. non-local or repulsive priors for an independent flexible mixture, discouraging duplicate or negligible components;
5. parametric-bootstrap tests for important presence decisions;
6. posterior-predictive checks.

The independent challenge model intentionally ignores the 1/2/4/16 parent structure:

\[
p_C(x)=\sum_{k=1}^{K}\pi_k f(x;\mu_k,\sigma_k,\gamma_k).
\]

Its role is to falsify ASMD assumptions. Agreement strengthens interpretation; disagreement is retained as a first-class result.

### 10.9 Parametric-bootstrap group test

To test whether group `q` is needed:

\[
H_0:\alpha_q=0,
\qquad
H_1:\alpha_q>0.
\]

Observed statistic:

\[
T_{obs}=2[\ell(\hat M_1)-\ell(\hat M_0)].
\]

For each bootstrap replicate:

1. simulate under fitted `M0` using its observation model;
2. rerun candidate generation, mask search, and fitting—not only a fixed-parameter local test;
3. calculate the replicate’s strongest competing statistic;
4. estimate a global p-value:

\[
p=\frac{1+\#\{T_b\ge T_{obs}\}}{B+1}.
\]

Repeating the search handles the look-elsewhere effect more honestly than testing only a preselected center and width.

### 10.10 Equal-portion hypotheses

Directly support constraints such as:

\[
\alpha_2=\alpha_4,
\]

\[
\alpha_2=\alpha_{16},
\]

and

\[
\alpha_2=\alpha_4=\alpha_{16}.
\]

Fit both constrained and unconstrained models, compare them with bootstrap-calibrated likelihood and Bayesian evidence, and report an interval on every difference:

\[
\Delta_{2,16}=\alpha_2-\alpha_{16}.
\]

“Equality not rejected” must not be phrased as proof of exact equality.

### 10.11 Posterior-predictive checks

Simulate replicated curves from posterior/final model draws and compare at least:

- number and persistence of modes;
- GSS raw and unique spectra;
- tail mass at configured quantiles;
- skewness and kurtosis;
- valley depth and read-boundary error mass;
- residual autocorrelation;
- local curvature and shoulders;
- per-bin deviance;
- relationships across P/E cycle, retention time, layer, and temperature.

A model fails PPC when observed statistics repeatedly lie outside the replicated distribution. This can reveal that a “2 group” is really one heavy-tailed state or that image-extraction artifacts remain.

### 10.12 Identifiability and template coherence

For normalized templates `a` and `b`, calculate whitened coherence:

\[
\rho_{ab}=
\frac{|a^TWb|}{\sqrt{(a^TWa)(b^TWb)}}.
\]

High coherence means their portions may trade off. Also report:

- condition number of the active design matrix;
- profile likelihood for every parent portion;
- posterior correlation matrix;
- bootstrap presence probability;
- child-resolution count separately from parent-group evidence.

Suggested states:

```simple
enum EvidenceState:
    Rejected
    NoiseLike
    Candidate
    Probable
    Confirmed
    Ambiguous
    NonIdentifiable
```

No fixed universal thresholds are embedded in the mathematics layer. Policy profiles define thresholds and preserve the underlying statistics.

### 10.13 ASMD pseudocode

```simple
fn asmd_reference_fit(
    data: NumericDataset,
    gss: GssSpectrum,
    cfg: AsmdConfig
) -> Result<AsmdResult, AnalysisError>:
    val noise = fit_noise_model(data, cfg.noise)
    val baseline_candidates = build_baseline_candidates(data, cfg.baseline)
    val masks = all_presence_masks(cfg.group_quantities)
    var fitted: [CandidateModel] = []

    for baseline in baseline_candidates:
        for mask in masks:
            for rigidity in cfg.rigidity_levels:
                for atom_family in cfg.atom_families:
                    for unknown_kind in cfg.unknown_models:
                        val seeds = build_multistart_seeds(gss, mask, cfg.seed_policy)
                        for seed in seeds:
                            val model = initialize_asmd(
                                data, mask, rigidity, atom_family,
                                unknown_kind, baseline, seed
                            )
                            val fit = varpro_fit(data, model, noise, cfg.optimizer)
                            if fit.is_valid():
                                fitted.push(score_candidate(data, fit, noise, cfg))

    val finalists = retain_distinct_finalists(fitted, cfg.finalist_policy)
    val challenge = fit_flexible_challenge_mixture(data, noise, cfg.challenge)
    val evidence = estimate_model_evidence(data, finalists, challenge, cfg.bayes)
    val bootstrap = bootstrap_presence_and_equality(data, finalists, cfg.bootstrap)
    val ppc = posterior_predictive_checks(data, finalists, challenge, cfg.ppc)

    Ok(resolve_or_mark_ambiguous(
        data, gss, finalists, challenge, evidence, bootstrap, ppc
    ))
```

---

## 11. SiZer-like multiscale significance

### 11.1 Role

This layer answers “at which positions and scales is there statistically supported increasing/decreasing/curvature structure?” It does not decide parent quantity.

Construct Gaussian scale space:

\[
L(x,h)=G_h*y.
\]

For mode/shoulder analysis, estimate derivatives:

\[
D_1(x,h)=\frac{\partial L}{\partial x},
\qquad
D_2(x,h)=\frac{\partial^2L}{\partial x^2}.
\]

At every `(x,h)`, classify the confidence interval of the derivative as positive, negative, or including zero. Link significant zero crossings and extrema across scales into ridges.

### 11.2 Outputs

```simple
class ScaleFeature:
    position: f64
    scale_min: f64
    scale_peak: f64
    scale_max: f64
    derivative_order: i32
    significance: f64
    persistence_octaves: f64
    kind: ScaleFeatureKind
```

Persistence:

\[
P=\log_2(h_{max}/h_{min}).
\]

This is evidence, not a universal binary rule. A coherent 16-group may have weak individual child ridges while its structured GSS response remains strong.

### 11.3 No-noise-reduction guarantee

Scale-space arrays are tagged as derived analysis views. They cannot be passed to final fitting accidentally without an explicit type conversion:

```simple
class RawObservationSeries: ...
class DerivedAnalysisSeries: ...
```

This type separation prevents smoothing from silently becoming the measured data.

---

## 12. NAND distribution analysis profile

### 12.1 Profile inputs

The NAND profile supports:

- raw per-cell Vt codes/voltages;
- read-retry cumulative counts;
- precomputed histograms;
- one curve per physical state;
- a summed/overlaid distribution requiring decomposition;
- repeated curves by block, wordline, layer, die, temperature, P/E cycle, retention age, read-disturb count, or program-disturb count.

```simple
class NandCondition:
    bits_per_cell: i32
    pe_cycles: i64
    retention_seconds: f64
    temperature_c: f64
    layer: i32
    wordline: i32
    block_id: text
    die_id: text
```

### 12.2 Physical state model

```simple
class NandStateSpec:
    ordinal: i32
    label: text              # ER, P1, ...
    logical_code: text       # product-specific mapping
    expected_order: i32
    atom_family: AtomFamilyKind
```

Default state counts:

| Cell type | Bits/cell | Physical states |
|---|---:|---:|
| SLC | 1 | 2 |
| MLC | 2 | 4 |
| TLC | 3 | 8 |
| QLC | 4 | 16 |

The mapping from physical state to logical bits is product-specific and configurable; never hard-code one Gray mapping as universal.

### 12.3 Read-retry histogram conversion

If `C(v)` is the cumulative number of cells changing decision by read-reference voltage `v`, an interval count can be formed by adjacent differences after orientation is established:

\[
h_i=|C(v_{i+1})-C(v_i)|.
\]

Required checks:

- monotonicity within expected count noise;
- duplicated/missing reference steps;
- saturation and clipping;
- orientation (increasing versus decreasing cumulative count);
- exposure/cell count consistency;
- voltage-code calibration.

Do not numerically differentiate without retaining the original cumulative trace and propagated uncertainty.

### 12.4 NAND-specific outputs

For every physical state or inferred group:

- total population portion;
- `mu`, `sigma`, variance, FWHM;
- skew/tail parameters;
- P/E-dependent mean shift and sigma widening;
- retention shift and widening;
- layer/wordline random effect;
- pairwise overlap coefficient;
- Bhattacharyya coefficient/distance;
- valley position and depth;
- optimal read-reference voltage under configured cost/prior;
- predicted raw bit error mass;
- left/right tail probabilities;
- confidence intervals and evidence state.

For two adjacent state densities `p_i` and `p_j` with priors/costs, an equal-cost Bayesian boundary solves:

\[
\pi_i p_i(v_{ref})=\pi_j p_j(v_{ref}).
\]

With asymmetric error costs, include the cost ratio explicitly.

### 12.5 Multi-condition hierarchical fit

Related curves should share information without being forced identical. A possible parameterization is:

\[
\mu_{s,c}=\mu_{s,0}
+\beta^{PE}_s g(PE_c)
+\beta^{ret}_s\log(1+t_c)
+\beta^{temp}_s T_c
+u^{layer}_{s,l(c)},
\]

\[
\log\sigma_{s,c}=a_{s,0}
+a^{PE}_s g(PE_c)
+a^{ret}_s\log(1+t_c)
+a^{temp}_s T_c
+v^{layer}_{s,l(c)}.
\]

`g(PE)` is selected from linear, log, power, or exponential saturation candidates by predictive evidence. This improves identification of weak overlapping states and directly measures evolution.

### 12.6 Integration with current NAND emulator

Use `std.hardware.nand_emu.physics` to generate deterministic fixtures for:

- known erase/program means and sigmas;
- controlled P/E widening;
- retention and disturb shifts;
- mixtures with seeded noise;
- exact no-noise tests (`sigma <= 0` path);
- reproducible combined 1+2+4+16 analysis fixtures.

The emulator remains an independent data generator. Analysis code must not call emulator internals to recover hidden truth during a fit.

### 12.7 NAND profile configuration

```simple
fn default_nand_analysis() -> NandAnalysisConfig:
    NandAnalysisConfig(
        physical_profile: NandProfile.qlc(),
        structured: StructuredSearchConfig(
            group_quantities: [1, 2, 4, 16],
            variation_count: 9
        ),
        atom_families: [
            AtomFamilyKind.Gaussian,
            AtomFamilyKind.NormalLaplace,
            AtomFamilyKind.StudentT
        ],
        preprocess_mode: PreprocessMode.AnalysisOnly,
        fit_against_raw: true,
        quality: AnalysisQuality.Reference
    )
```

---
## 13. Image graph-to-numeric digitizer

### 13.1 Design principle

The chart digitizer is a reusable library independent of NAND analysis. It converts a raster chart into numeric series plus uncertainty and evidence. The pipeline must expose intermediate artifacts:

```text
image
  ├── plot-region/axis hypotheses
  ├── text and legend regions
  ├── grid/axis/decoration masks
  ├── color/style clusters
  ├── per-series pixel likelihood maps
  ├── traced paths with gaps/crossings
  ├── numeric calibration
  ├── numeric series + uncertainty
  └── render-back validation overlay
```

A direct VLM chart-to-table result may be retained as a candidate provider output, but it is not accepted without geometric calibration and render-back checks.

### 13.2 Supported images

Initial native support uses the existing bounded PNG decoder. The public interface should be format-neutral:

```simple
trait RasterImageDecoder:
    fn decode(bytes: [u8], limits: ImageLimits) -> Result<RasterImage, ImageError>
```

Providers may add JPEG, WebP, TIFF, BMP, or PDF-page raster input. The decoded canonical format is unpremultiplied RGBA/ARGB with known color space where available.

### 13.3 Plot-region and axis detection

Generate several plot-region candidates from:

- long horizontal and vertical line segments;
- dense rectangular data regions;
- tick-mark repetition;
- OCR text placement around candidate borders;
- background/color transitions;
- user-supplied corners.

Use robust line detection rather than one exact Hough threshold:

1. edge probability;
2. line-segment detector or probabilistic Hough candidates;
3. orientation clustering near 0° and 90°;
4. robust rectangle fitting;
5. score by tick/text consistency and enclosed curve density.

Represent alternatives:

```simple
class PlotRegionHypothesis:
    rect: PixelRect
    x_axis_line: PixelLine
    y_axis_line: PixelLine
    score: f64
    evidence: [EvidenceItem]
```

If the top two hypotheses are close, return an ambiguity requiring manual selection or retain both through calibration.

### 13.4 Text and legend handling

Define a provider boundary:

```simple
trait ChartTextProvider:
    fn detect_text(image: RasterImage) -> Result<[TextRegion], ChartTextError>
```

Providers:

- `manual`: user supplies labels/ticks;
- `none`: geometry-only extraction with pixel coordinates;
- `ocr_sffi`: OCR engine through a narrow typed SFFI;
- `platform_ocr`: optional OS provider;
- `vlm`: optional semantic reading/legend association;
- future pure-Simple OCR.

Text regions are used for both semantics and masking. The geometry path should still detect likely text-like connected components when OCR cannot read them.

Legend association uses multiple cues:

- color distance between swatch/sample and curve;
- dash and marker style;
- spatial proximity inside a legend region;
- OCR/VLM label evidence;
- global one-to-one or many-to-one assignment cost.

Never assign a label solely from nearest Euclidean position when multiple legends or inline labels are present.

### 13.5 Color representation

Exact RGB matching is too fragile under antialiasing, scanning, and JPEG compression. Convert pixels to a perceptual color space, preferably CIELAB or OKLab, and use a color likelihood:

\[
p(c\mid k)\propto
\exp\left(-\frac{\Delta E(c,\bar c_k)^2}{2\tau_k^2}\right).
\]

The Simple reference may initially implement sRGB → linear RGB → XYZ → Lab and CIE76 distance; later providers may add CIEDE2000.

Use alpha, saturation, local contrast, and plot background estimates. Cluster colors only inside candidate plot regions after excluding obvious text/axis/grid masks.

When colors are absent or nearly identical, switch from color-first tracing to a multi-path style/geometry mode using stroke width, dash period, markers, tangent continuity, and global path assignment. The result must lower confidence rather than pretend same-color crossings are as easy as separated colors.

### 13.6 Decoration rejection

The user specifically requires robustness against letters, straight lines, and dashed lines. Classify components rather than deleting by one threshold.

#### Text/letters

Evidence:

- OCR/text bounding boxes;
- connected-component stroke width;
- compactness and repeated glyph height;
- location outside/near plot borders;
- disconnected high-curvature shapes;
- dark neutral color unlike known series.

Text masks should be dilated only enough to remove antialiased fringes; excessive dilation can erase curves crossing labels.

#### Axes and grid lines

Evidence:

- nearly horizontal/vertical orientation;
- very long support;
- repeated equally spaced parallels;
- neutral low-saturation color;
- connection to tick marks;
- constant one-pixel or thin stroke;
- plot-border coincidence.

Do **not** remove all long straight lines: a valid data series may be straight or dashed. A line is decoration only when its combined role score is stronger than its series score.

#### Legend sample lines

Detect a legend region, associate swatches to labels, and exclude the short sample segments from plot data. If a legend overlays the plot, preserve an occlusion mask and allow trajectories to bridge it with uncertainty.

### 13.7 Solid-line extraction

For each candidate series `k`, construct a pixel likelihood map:

\[
L_k(u,v)=
L_{color}L_{edge}L_{stroke}L_{not\_text}L_{not\_grid}.
\]

Trace one or more y positions over x columns using dynamic programming/Viterbi:

\[
E(y_{1:W})=
\sum_x -\log L_k(x,y_x)
+\lambda_1|y_x-y_{x-1}|
+\lambda_2|y_x-2y_{x-1}+y_{x-2}|.
\]

Allow a small set of candidate y values per x, plus an `occluded` state. Use subpixel center estimates from a stroke’s vertical intensity/color profile.

For non-function curves or loops, use graph/skeleton tracing instead of the x-monotone path assumption and mark that the result cannot be represented as ordinary `y(x)` without segmentation.

### 13.8 Dashed and dotted lines

A dashed curve has intentional missing pixels. Extend the path model with visible/hidden states:

```text
Visible -> Visible
Visible -> Gap
Gap     -> Gap
Gap     -> Visible
```

Gap cost depends on:

- expected dash period and duty cycle;
- color/style agreement before and after the gap;
- tangent/curvature continuity;
- maximum unexplained gap length;
- whether the gap coincides with text, another curve, or a legend overlay.

Estimate dash pattern from connected run lengths along candidate trajectories. Permit several patterns because rasterization changes apparent lengths.

A long dashed **straight data line** must survive grid rejection when its color, legend style, periodic gap model, and plot-region position support a series interpretation.

### 13.9 Crossings and overlaps

At crossings, local segmentation can merge curves. Use global assignment:

- preserve color identity if colors differ;
- preserve dash/marker style if colors match;
- compare incoming and outgoing tangents;
- minimize curvature through the crossing;
- maintain trajectory ordering where physically justified;
- use min-cost flow, linear programming, or beam search over ambiguous junctions;
- retain multiple hypotheses when costs are close.

This reflects line-chart research showing that point detection alone does not solve association in dense overlapping charts.

### 13.10 Axis calibration

An axis calibration maps pixel coordinate `p` to numeric value.

For a linear axis:

\[
x=a_x p+b_x.
\]

For a logarithmic axis:

\[
\log_b x=a_x p+b_x,
\qquad
x=b^{a_xp+b_x}.
\]

Fit from OCR/manual tick pairs with robust regression (RANSAC or M-estimator), then use all accepted ticks for least-squares refinement. Report residuals and rejected ticks.

Automatic linear/log choice evaluates:

- spacing of numeric tick values in value and log domains;
- pixel-spacing regularity;
- labels such as powers of ten;
- predictive calibration residual.

At least two distinct ticks are required for each affine axis. More ticks are strongly preferred. With fewer, return pixel-coordinate series or require manual calibration rather than invent values.

### 13.11 Mapping and point uncertainty

For each x sample/pixel column, map the traced center and vertical stroke interval to numeric y. Propagate:

- path ambiguity;
- stroke thickness;
- color segmentation uncertainty;
- axis calibration covariance;
- gap interpolation;
- downsampling/resampling error.

Approximate local propagation:

\[
\sigma_y^2\approx
\left(\frac{dy}{dp}\right)^2\sigma_p^2
+J_{cal}\Sigma_{cal}J_{cal}^T.
\]

Each output point stores confidence and flags:

```simple
enum PointFlag:
    Observed
    Antialiased
    InterpolatedDashGap
    OccludedByText
    OccludedByCurve
    CrossingAmbiguous
    Extrapolated
    ManualCorrection
```

### 13.12 Render-back validation

After digitization:

1. project numeric series back to image pixels;
2. render with estimated color/style/width;
3. compare against the source inside the plot region;
4. output overlay and difference masks;
5. calculate coverage and contamination metrics.

Metrics:

- curve-pixel precision/recall/F1;
- mean/95th-percentile perpendicular pixel error;
- calibration residual;
- visible-segment coverage;
- unsupported reconstructed length;
- per-series crossing/occlusion ambiguity;
- end-to-end numeric error on synthetic fixtures.

A chart-to-table provider result that cannot render back near the observed curves is rejected or downgraded.

### 13.13 Manual correction manifest

Scientific digitization requires reproducible correction, not ad-hoc editing. Store operations:

```text
set_plot_rect
set_axis_tick(pixel, value)
accept_text_region
ignore_region
seed_series_color
join_segments
split_segment
set_dash_pattern
move_path_point
set_legend_label
```

The manifest is replayable against the source hash. Corrections become provenance and receive `ManualCorrection` flags.

### 13.14 Digitization pseudocode

```simple
fn digitize_line_chart(
    image: RasterImage,
    cfg: ChartDigitizeConfig,
    text_provider: ChartTextProvider
) -> Result<DigitizedChart, ChartDigitizeError>:
    val plot_candidates = detect_plot_regions(image, cfg.plot_detection)
    val text = text_provider.detect_text(image).or_default([])
    val plot = choose_or_retain_plot_hypotheses(plot_candidates, text, cfg)
    val axes = detect_axes_ticks_and_grid(image, plot, text, cfg)
    val calibration = calibrate_axes(axes, text, cfg.manual_ticks)

    val decoration = classify_decorations(image, plot, axes, text, cfg)
    val color_clusters = cluster_series_colors(image, plot, decoration, cfg.color)
    var series: [DigitizedSeries] = []

    for cluster in color_clusters:
        val likelihood = build_curve_likelihood(image, plot, decoration, cluster, cfg)
        val segments = trace_visible_segments(likelihood, cfg.path)
        val paths = connect_segments_with_dash_and_occlusion_model(
            segments, likelihood, cluster, cfg.gaps
        )
        for path in resolve_crossings(paths, series, image, cfg.crossings):
            series.push(map_path_to_numeric(path, calibration, cfg.resampling))

    val corrected = apply_correction_manifest(series, cfg.corrections)
    val validation = render_back_and_validate(image, plot, corrected, calibration, cfg)
    Ok(DigitizedChart(
        image: image.reference,
        plot_region: plot.rect,
        x_calibration: calibration.x,
        y_calibration: calibration.y,
        series: corrected,
        text_regions: text,
        ignored_regions: decoration.ignored,
        validation: validation
    ))
```

---

## 14. Image graph-to-text and LLM-oriented output

### 14.1 Principle

An LLM should receive exact numeric facts and uncertainty, not be asked to estimate a curve from a raster when the system already has numbers. The image remains available for visual verification, but text output is generated from the canonical numeric result.

Produce four coordinated outputs:

1. **canonical SDN/JSON** — full machine-readable structure;
2. **CSV tables** — extracted series and GSS cells;
3. **compact deterministic text** — token-bounded LLM context;
4. **SVG/PNG plots** — human and multimodal inspection.

### 14.2 GraphText v1

Example:

```text
graph_text_version: 1
source:
  kind: image
  sha256: ...
  plot_region_px: [84, 42, 941, 711]
axes:
  x: {name: "threshold voltage", unit: "V", scale: linear, min: -2.0, max: 8.0, calibration_rmse_px: 0.42}
  y: {name: "density", unit: "", scale: log10, min: 1e-8, max: 1.0, calibration_rmse_px: 0.63}
series:
  - id: red
    label: "P1"
    color: "#d92d20"
    style: dashed
    point_count: 1024
    observed_fraction: 0.91
    uncertain_ranges: [[3.14,3.29],[5.00,5.08]]
    landmarks:
      max: {x: 1.82, y: 0.313}
      half_max_left: 1.47
      half_max_right: 2.16
analysis:
  known_group_portions: {1: 0.071, 2: 0.297, 4: 0.301, 16: 0.309}
  unknown_portion: 0.022
  equal_portion_test_2_4_16: {difference_supported: false, p_bootstrap: 0.38}
  evidence: {model: "1+2+4+16+U", state: "confirmed", ppc: "pass"}
gss_top_peaks:
  - {quantity: 16, variation: 5, center: 8.31, raw_match: 0.97, unique_llr: 143.2}
  - {quantity: 4, variation: 6, center: 6.12, raw_match: 0.94, unique_llr: 101.4}
warnings:
  - "children 7-11 of quantity-16 group are not individually resolved"
```

### 14.3 Numeric-series compression for LLM context

Never discard the full series; create an LLM view using:

- axis metadata;
- exact extrema, moments, crossings, valleys, and quantiles;
- Douglas-Peucker or error-bounded piecewise-linear knots;
- fixed-bin summaries;
- uncertain/occluded intervals;
- top GSS peaks and final ASMD groups;
- residual diagnostics.

Compression must include an absolute and relative reconstruction-error bound. A token budget selects fewer knots but never changes summary values.

### 14.4 Required LLM warnings

The generated text must distinguish:

- `not_present`;
- `not_detected`;
- `ambiguous`;
- `non_identifiable`;
- `outside_image_resolution`;
- `digitization_uncertain`;
- `model_family_mismatch`.

It must never state that a physical group is absent merely because individual children are not visually resolved.

### 14.5 SVG metadata

GSS and reconstruction SVGs should include stable IDs and embedded data attributes:

```xml
<circle id="gss-q16-v5"
        data-quantity="16"
        data-width-factor="1.0"
        data-spacing-factor="1.0"
        data-raw-match="0.97"
        data-unique-llr="143.2" ... />
```

This supports deterministic testing, accessibility, and direct extraction by tools without OCR.

---

## 15. Output plots

The analysis command generates, as configured:

| Output | Purpose |
|---|---|
| `input.svg/png` | normalized input view |
| `digitized_overlay.png` | source image with traced paths, axes, masks, and uncertainty |
| `series.svg` | reconstructed numeric curves |
| `scale_space.svg` | SiZer-like position/scale significance map |
| `gss_raw.svg` | FFT-like raw match spectrum |
| `gss_unique.svg` | unique likelihood spectrum after joint fitting |
| `gss_position.svg` | template-versus-position heatmap |
| `asmd_components.svg` | known parent/child components and unknown residual |
| `asmd_sum_residual.svg` | observed, predicted, and residual graphs |
| `nand_boundaries.svg` | state distributions and read-reference thresholds |
| `ppc.svg` | observed statistics against posterior predictive distributions |

Extract the common numeric-axis/SVG primitives from the current office chart code instead of copying private helpers into the analysis app.

---

## 16. Storage and search architecture

### 16.1 Authoritative data

The authoritative record is exact numeric and structured data, not a vector embedding.

Recommended layers:

```text
raw source object
  ├── original CSV/XLSX/image
  ├── source hash
  └── correction/config manifests

numeric columnar data
  ├── x, y, uncertainty, flags
  └── repeated conditions

relational/SDN analysis records
  ├── models, groups, components, evidence
  └── provenance and versions

secondary search descriptors
  ├── resampled shape vector
  ├── GSS vector
  ├── ASMD parameter vector
  └── hierarchy/condition vector
```

### 16.2 File formats

- **SDN**: canonical Simple-native metadata and analysis result.
- **CSV**: interoperability and small exported point tables.
- **XLSX/ODS**: source/interchange through existing office codecs, not the canonical analysis store.
- **Arrow IPC**: optional zero-copy/interprocess columnar batches when/if the Simple Arrow subset is implemented.
- **Parquet**: recommended long-term columnar store for large datasets, reached through an optional provider initially.
- **PNG/SVG**: images and plots; SVG is preferred for generated plots because values can remain structural text/attributes.

Arrow’s format is designed for adjacent column data, vectorization, and zero-copy relocation; Parquet complements it as compressed long-term columnar storage. A minimal first release may use SDN + binary f64 arrays and add Arrow/Parquet through a provider without blocking analysis correctness.

### 16.3 Relational schema

```text
measurement(
  id, source_hash, source_kind, timestamp,
  x_axis, y_axis, observation_kind, condition_id,
  analysis_version, config_hash
)

series(
  id, measurement_id, label, color, line_style,
  point_storage_ref, digitization_confidence
)

model_fit(
  id, series_id, model_mask, rigidity, atom_family,
  baseline_kind, log_likelihood, predictive_score,
  evidence, ppc_status, identifiability_status
)

parent_group(
  id, fit_id, quantity, portion, portion_ci,
  center, spacing, width, existence_support
)

child_component(
  id, parent_group_id, ordinal, weight,
  mu, sigma, shape, confidence, resolution_state
)

gss_cell(
  series_id, quantity, variation_id, center,
  raw_match, raw_llr, unique_llr, amplitude_seed
)

digitization_region(
  series_id, kind, pixel_rect_or_path, confidence, reason
)
```

### 16.4 Vector search

Vector search is a secondary candidate-retrieval layer. Store multiple named vectors rather than one opaque embedding:

1. `shape_vector`: normalized resampled curve;
2. `gss_vector`: flattened raw/unique GSS cells;
3. `asmd_vector`: sorted parent portions and child parameters with masks;
4. `condition_vector`: P/E, retention, temperature, layer metadata;
5. optional learned embedding.

Search flow:

```text
metadata/condition filter
       ↓
approximate vector retrieval
       ↓
exact alignment and numeric distance
       ↓
ASMD/GSS-aware reranking
       ↓
final neighbors with explanation
```

A graph database is only warranted when relationship traversal dominates—for example, tracking one component’s split/merge/evolution across cycles. It is not the primary representation for curve similarity.

| Technology | Primary responsibility | Do not use it as |
|---|---|---|
| SDN/relational tables | authoritative metadata, models, evidence, provenance | dense raw-array engine by itself |
| Parquet/columnar files | large exact numeric datasets and scans | mutable transactional graph |
| Arrow/contiguous arrays | in-memory/interprocess computation | sole long-term archive |
| Vector index | fast similar-shape/GSS candidate retrieval | final scientific distance or source of truth |
| Graph database/edge table | provenance and split/merge/evolution traversal | numerical curve-similarity engine |
| PNG/SVG | visual evidence and overlays | authoritative numeric result when a table exists |

---
## 17. Simple package and ownership design

### 17.1 Ownership boundaries

The feature crosses data ingest, science math, imaging, plotting, and NAND. Keep dependencies one-directional:

```text
std.common.image / app.office codecs
                │
                ▼
std.common.chart_digitize
                │
                ▼
std.common.science_distribution
                │
                ▼
std.hardware.nand_analysis
                │
                ▼
app.dist_analyze CLI / GUI / LLM tool
```

`science_distribution` accepts numeric data only and cannot import chart-image logic. `chart_digitize` cannot import NAND. `nand_analysis` adds domain configuration and derived metrics over the generic distribution library.

### 17.2 Proposed source tree

```text
src/lib/common/science_distribution/
  __init__.spl
  types.spl
  errors.spl
  validate.spl
  streaming_stats.spl
  integration.spl
  interpolation.spl
  noise.spl
  baseline.spl
  atom.spl
  atom_gaussian.spl
  atom_student_t.spl
  atom_normal_laplace.spl
  atom_skew_normal.spl
  scale_space.spl
  sizer.spl
  template_bank.spl
  gss.spl
  gss_peaks.spl
  nnls.spl
  simplex.spl
  trust_region.spl
  varpro.spl
  asmd_model.spl
  asmd_fit.spl
  challenge_mixture.spl
  bootstrap.spl
  posterior_predictive.spl
  identifiability.spl
  model_compare.spl
  summarize.spl
  provider.spl

src/lib/common/chart_digitize/
  __init__.spl
  types.spl
  errors.spl
  raster_adapter.spl
  plot_region.spl
  edges.spl
  line_segments.spl
  connected_components.spl
  color_space.spl
  color_cluster.spl
  decoration.spl
  text_provider.spl
  legend.spl
  axis.spl
  calibration.spl
  curve_likelihood.spl
  curve_trace.spl
  dash_model.spl
  crossings.spl
  uncertainty.spl
  corrections.spl
  render_back.spl
  validate.spl
  to_dataset.spl

src/lib/hardware/nand_analysis/
  __init__.spl
  profile.spl
  state_mapping.spl
  read_retry.spl
  threshold_fit.spl
  evolution.spl
  read_boundary.spl
  error_mass.spl
  report.spl
  emulator_fixture.spl

src/lib/common/analysis_io/
  __init__.spl
  dataset_sdn.spl
  dataset_csv.spl
  sheet_adapter.spl
  result_sdn.spl
  result_json.spl
  llm_graph_text.spl
  point_binary.spl
  parquet_provider.spl

src/lib/common/analysis_plot/
  __init__.spl
  svg_axis.spl
  svg_line.spl
  svg_heatmap.spl
  svg_gss.spl
  svg_components.spl
  svg_overlay.spl

src/app/dist_analyze/
  main.spl
  cli.spl
  command_digitize.spl
  command_analyze.spl
  command_nand.spl
  command_compare.spl
  config.spl
  output.spl
```

Before creating `analysis_plot`, inspect whether the office chart helpers can be safely generalized and moved into a common plot layer without breaking existing APIs. Avoid reverse dependencies from a standard library to `app.office`.

### 17.3 Optional provider tree

```text
src/lib/common/chart_digitize/providers/
  manual_text.spl
  no_text.spl
  ocr_sffi.spl
  segmentor_sffi.spl
  vlm_legend.spl

src/lib/common/science_distribution/providers/
  direct_cpu.spl
  fft_tensor.spl
  cuda.spl
  bayes_sffi.spl
  parquet_sffi.spl
```

The reference implementation remains Simple. SFFI providers must expose capability/version information and fail closed when unavailable.

---

## 18. Public Simple APIs

### 18.1 One-call API

```simple
fn analyze_distribution_file(
    path: text,
    cfg: DistributionAnalysisConfig
) -> Result<DistributionAnalysisBundle, AnalysisError>
```

It dispatches by file type through registered adapters, but the selected adapter and inferred columns are included in the result.

### 18.2 Core API

```simple
fn load_numeric_dataset(
    source: AnalysisSource,
    cfg: IngestConfig
) -> Result<NumericDataset, AnalysisError>

fn digitize_chart(
    image: RasterImage,
    cfg: ChartDigitizeConfig
) -> Result<DigitizedChart, ChartDigitizeError>

fn compute_scale_significance(
    series: NumericSeries,
    cfg: ScaleSpaceConfig
) -> Result<ScaleSignificance, AnalysisError>

fn gss_transform(
    series: NumericSeries,
    cfg: GssConfig
) -> Result<GssSpectrum, AnalysisError>

fn asmd_fit(
    series: NumericSeries,
    gss: GssSpectrum,
    cfg: AsmdConfig
) -> Result<AsmdResult, AnalysisError>

fn analyze_nand_distribution(
    dataset: NumericDataset,
    condition: NandCondition,
    cfg: NandAnalysisConfig
) -> Result<NandAnalysisResult, AnalysisError>

fn render_analysis_bundle(
    result: DistributionAnalysisBundle,
    cfg: OutputConfig
) -> Result<[OutputArtifact], AnalysisError>
```

### 18.3 Configuration

```simple
class DistributionAnalysisConfig:
    ingest: IngestConfig
    preprocess: PreprocessConfig
    scale_space: ScaleSpaceConfig
    gss: GssConfig
    asmd: AsmdConfig
    nand: NandAnalysisConfig?
    digitize: ChartDigitizeConfig
    output: OutputConfig
    quality: AnalysisQuality
```

Configurations are serializable to SDN and hashable. CLI defaults are produced by functions, not duplicated string constants.

### 18.4 Template-bank API

```simple
class TemplateVariation:
    id: text
    width_factor: f64
    spacing_factor: f64
    child_weight_pattern: [f64]
    atom_family: AtomFamilyKind
    shape_parameter: f64

class GssTemplateFamily:
    quantity: i32
    canonical_positions: [f64]
    variations: [TemplateVariation]

class GssTemplateBank:
    families: [GssTemplateFamily]
    normalization: TemplateNormalization
```

Default constructor:

```simple
fn gss_default_bank(
    quantities: [i32] = [1, 2, 4, 16],
    variation_count: i32 = 9
) -> Result<GssTemplateBank, AnalysisError>
```

If `variation_count` is not exactly supported by a named policy, require an explicit generation policy rather than quietly truncating.

### 18.5 Provider contract

```simple
trait CorrelationProvider:
    fn name() -> text
    fn capabilities() -> CorrelationCapabilities
    fn correlate(signal: [f64], template: [f64], mode: CorrelationMode) 
        -> Result<[f64], AnalysisError>

trait NonlinearOptimizer:
    fn solve(problem: SeparableFitProblem, cfg: OptimizerConfig)
        -> Result<OptimizerResult, AnalysisError>

trait ChartSegmentProvider:
    fn segment(image: RasterImage, plot: PixelRect)
        -> Result<[SeriesMask], ChartDigitizeError>
```

Providers must not return sentinel handles such as zero as a successful result. Convert low-level SFFI failures immediately to typed errors.

---

## 19. CLI design

### 19.1 Numeric input

```bash
simple dist analyze data.csv \
  --x Vt --y count \
  --observation histogram-count \
  --groups 1,2,4,16 \
  --quality reference \
  --out out/
```

Wide multi-series:

```bash
simple dist analyze sweep.xlsx \
  --sheet Retention \
  --x A2:A4097 \
  --y B2:E4097 \
  --labels B1:E1 \
  --joint-by-series \
  --out out/
```

### 19.2 NAND

```bash
simple dist nand read_retry.csv \
  --cell qlc \
  --input cumulative-read-retry \
  --ref-column voltage_code \
  --count-columns ER,P1,P2,P3,P4,P5,P6,P7,P8,P9,P10,P11,P12,P13,P14,P15 \
  --groups 1,2,4,16 \
  --atom gaussian,normal-laplace,student-t \
  --quality reference \
  --out nand_result/
```

TLC remains valid:

```bash
simple dist nand tlc.xlsx --cell tlc --states 8 --groups 1,2,4,16 ...
```

### 19.3 Image digitization only

```bash
simple chart digitize graph.png \
  --auto-plot-region \
  --axis auto \
  --series all \
  --trace solid,dashed,dotted \
  --csv extracted.csv \
  --sdn extracted.sdn \
  --overlay overlay.png \
  --llm-text graph.txt
```

Manual calibration:

```bash
simple chart digitize graph.png \
  --plot-rect 84,42,941,711 \
  --x-tick 103:-2.0 --x-tick 886:8.0 \
  --y-tick 692:1e-8 --y-tick 71:1.0 \
  --y-scale log10 \
  --color-seed red:210,45,32 \
  --corrections graph.corrections.sdn \
  --out extracted/
```

### 19.4 Image-to-analysis

```bash
simple dist analyze graph.png \
  --digitize \
  --profile nand \
  --groups 1,2,4,16 \
  --preprocess analysis-only \
  --quality reference \
  --out result/
```

### 19.5 GSS-only mode

```bash
simple dist spectrum data.csv \
  --groups 1,2,4,16 \
  --variations default-9 \
  --metric raw,unique,llr \
  --svg gss.svg \
  --csv gss.csv \
  --llm-text gss.txt
```

---

## 20. Result schema

```simple
class DistributionAnalysisBundle:
    dataset: NumericDataset
    digitization: DigitizedChart?
    scale_significance: [ScaleSignificance]
    gss: [GssSpectrum]
    asmd: [AsmdResult]
    nand: NandAnalysisResult?
    diagnostics: AnalysisDiagnostics
    artifacts: [OutputArtifact]
    provenance: Provenance
```

### 20.1 Parent group

```simple
class ParentGroupResult:
    quantity: i32
    portion: f64
    portion_interval: IntervalF64
    center: f64
    spacing: f64
    width: f64
    atom_family: AtomFamilyKind
    evidence_state: EvidenceState
    bootstrap_p: f64
    bootstrap_presence: f64
    coherence_max: f64
    children: [ChildComponentResult]
```

### 20.2 Diagnostics

```simple
class AnalysisDiagnostics:
    residual_summary: ResidualSummary
    model_comparison: [ModelEvidence]
    posterior_predictive: PpcResult
    identifiability: IdentifiabilityResult
    input_warnings: [AnalysisWarning]
    digitization_warnings: [AnalysisWarning]
    conflicts: [AnalysisConflict]
```

A result is incomplete unless it reports model conflicts and warnings alongside the chosen model.

---

## 21. Reference numeric algorithms

### 21.1 Stable descriptive statistics

The current array statistics are adequate for basic use but include simple two-pass and quadratic-sort code. Add independent stable, streaming primitives where analysis volume and reproducibility matter:

- Welford/Chan mean and variance;
- compensated/Kahan or Neumaier summation;
- weighted moments;
- weighted quantiles with a documented method;
- log-sum-exp;
- stable normal PDF/CDF/tail functions;
- incomplete beta if Beta atoms are implemented;
- error function and log-CDF for tail likelihoods.

Do not silently change current public semantics; introduce a science-analysis module with typed errors and numerical contracts.

### 21.2 Nonnegative least squares

Implement a small reliable active-set reference first. Required properties:

- `x >= 0` within tolerance;
- KKT residual report;
- optional `sum(x)=1`;
- weighted design matrix;
- rank/condition diagnostics;
- deterministic pivot tie-breaking;
- no mutation of input arrays.

Cross-check against LAPACK-backed and independent Python/R references during development.

### 21.3 Trust-region nonlinear fitting

Required features:

- parameter bounds;
- robust loss option for non-count data;
- finite-difference Jacobian reference;
- analytic/automatic Jacobian provider;
- step acceptance diagnostics;
- convergence by gradient, step, and objective;
- maximum-evaluation status distinct from convergence;
- profile-likelihood scanning.

### 21.4 Numerical integration

Histogram likelihoods require stable CDF differences. Provide:

- analytic Gaussian CDF difference;
- log-space tail difference;
- adaptive Gauss-Kronrod/reference quadrature for arbitrary atom families;
- cached standardized CDF tables where permitted;
- explicit integration error in diagnostics.

### 21.5 Randomness

Bootstrap and Bayesian routines require:

- counter-based or splittable deterministic RNG streams;
- stable substream derivation from `(source_hash, config_hash, replicate_id)`;
- Poisson, normal, categorical, Student-t, and Dirichlet samplers;
- recorded seed and RNG algorithm version.

---

## 22. Optional acceleration without changing semantics

Although speed is not the selection priority, the architecture should permit acceleration:

- direct convolution for small kernels;
- FFT correlation for large template banks;
- batched tensor/GPU correlation;
- GPU responsibility/likelihood reductions;
- batched bootstrap replicates;
- GPU vector search for secondary retrieval.

The reference result is defined by tolerances, not bitwise equality where backend arithmetic differs. Every accelerated provider must pass:

- direct-versus-FFT correlation tests;
- CPU-versus-GPU GSS peak equivalence;
- fitted portion/parameter tolerance tests;
- identical evidence-state decisions on a frozen corpus;
- explicit fallback when capabilities are absent.

Do not couple the public GSS name to FFT. FFT is one correlation backend, not the mathematical definition.

---

## 23. Security and robustness

### 23.1 Untrusted files

CSV/XLSX/images are untrusted inputs. Enforce:

- bounded row, column, cell-string, image-pixel, and decompressed-byte limits;
- archive expansion limits for XLSX/ODS;
- no formula execution during analysis ingest;
- explicit handling of external workbook links;
- bounded OCR/model execution;
- path traversal rejection;
- output escaping for SVG/HTML/text;
- no embedded source image scripts or external SVG references.

### 23.2 Numerical attacks and pathological data

Reject or isolate:

- NaN/infinity unless explicitly permitted as missing;
- zero/negative bin widths;
- nonmonotonic edges;
- all-zero data;
- singular axis calibration;
- unbounded sigma collapse;
- a component with vanishing variance and one-bin mass;
- huge likelihood caused by numerical underflow/overflow;
- duplicate templates and design-matrix rank collapse.

### 23.3 Resource budgets

Even `reference` mode requires configurable upper bounds and a typed `BudgetExceeded` result, not termination or partial success masquerading as completion.

---
## 24. Verification and test strategy

### 24.1 Test levels

| Level | Scope |
|---|---|
| Unit | math primitives, atom PDFs/CDFs, calibration, color conversion, path costs, parsers/adapters |
| Property | normalization, nonnegative portions, reconstruction invariants, monotonic CDFs, deterministic seeds |
| Differential | Simple versus independent Python/R/SciPy/OpenCV development oracles |
| Synthetic integration | generated curves/charts with exact ground truth |
| NAND integration | emulator/read-retry fixtures and condition sweeps |
| Image corpus | solid/dashed/dotted, crossings, text, grid, legend, compression, linear/log axes |
| Statistical calibration | false-positive rate, interval coverage, model-selection power |
| End-to-end | source file → numeric result → plots/text → reload/reproduce |
| Backend parity | pure Simple CPU versus FFT/SFFI/GPU providers |

### 24.2 Synthetic distribution matrix

Generate exact cases including:

- each of `1`, `2`, `4`, `16` alone;
- every nonempty subset of `{1,2,4,16}`;
- the worst case `1+2+4+16`;
- equal parent portions for 2/4/16;
- highly unequal parent portions;
- equal and unequal child weights;
- regular and distorted spacing;
- common and unequal widths;
- separations from clearly resolved to practically non-identifiable;
- Gaussian, Student-t, Normal-Laplace, skew-normal, and contaminated tails;
- constant/linear/spline baselines;
- Gaussian, Poisson, Poisson-Gaussian, and empirical replicate noise;
- no-noise exact reconstruction;
- unknown 3-, 5-, 8-, and arbitrary spline groups;
- clipped/saturated/truncated ranges;
- irregular x sampling and variable bin widths;
- repeated condition sweeps with known drift/widening laws.

For each case, save truth, seed, raw observations, and expected evidence class.

### 24.3 Statistical calibration tests

A scientific test suite must test distributions of outcomes, not only one fixed array.

Required campaigns:

1. **Null false positives:** under no extra group, global bootstrap tests meet the configured Type-I error within Monte Carlo tolerance.
2. **Coverage:** nominal 90/95/99% intervals achieve measured coverage on representative parameter grids.
3. **Power:** quantify detection probability as a function of parent portion, overlap, count/exposure, and noise.
4. **Equality test:** calibrate `alpha_2 = alpha_4 = alpha_16` under true equality and controlled deviations.
5. **Family mismatch:** verify that heavy-tail cases are not systematically labeled as additional structured groups without warning.
6. **Identifiability:** cases below resolution limits return broad/multimodal intervals or `NonIdentifiable`, not overconfident point estimates.
7. **Look-elsewhere:** repeat the complete location/width/template search in null simulations.

### 24.4 GSS tests

- analytical matched-filter amplitude against hand-computed vectors;
- scale invariance under expected normalization;
- translation peak location;
- direct versus FFT correlation;
- default bank has nine **distinct** templates per quantity;
- quantity-1 special bank contains no spacing duplicates;
- neighboring variation peaks cluster into one continuous candidate;
- raw GSS shows expected cross-talk while unique GSS suppresses explained templates;
- SVG metadata exactly matches SDN/CSV cells;
- LLM text top-k ordering and values are deterministic.

### 24.5 ASMD tests

- all 16 presence masks are evaluated in default exhaustive mode;
- parent portions remain nonnegative and sum correctly;
- equal 2/4/16 portions are recovered even when 16 children are individually weak;
- child-resolution state is independent of parent existence state;
- unknown mass captures an unexpected group rather than distorting known groups;
- label canonicalization is stable across initializations;
- all retained local modes are reported when evidence is close;
- constraint relaxation occurs only when justified;
- VarPro objective matches direct optimization on small fixtures;
- profile likelihood and bootstrap intervals contain truth at calibrated rates;
- posterior predictive failures are not ignored by final resolver.

### 24.6 Chart synthetic generator

Build a pure-Simple chart generator using the common SVG/PNG pipeline. Randomize:

- canvas and plot dimensions;
- linear/log axes and tick formats;
- fonts, labels, legends, inline labels;
- solid, dashed, dotted, marker, and mixed styles;
- line widths, opacity, antialiasing, and color distance;
- horizontal/vertical grid lines;
- straight and curved data lines;
- crossings and long overlaps;
- legend overlay occlusions;
- annotations/arrows/text inside plot;
- noise, blur, scaling, JPEG-like blocking provider, and scan skew;
- white, gray, colored, and textured backgrounds.

The generator emits exact source paths and semantic regions. It is both a test oracle and a possible synthetic training-data source for optional learned providers.

### 24.7 Image acceptance metrics

Suggested initial targets, evaluated separately by corpus difficulty:

| Metric | Clean synthetic | Noisy/compressed | Dense crossing |
|---|---:|---:|---:|
| Axis calibration median relative error | ≤0.1% | ≤0.5% | ≤0.5% |
| Curve median y error as plot-height fraction | ≤0.2% | ≤1.0% | ≤1.5% |
| 95th-percentile y error | ≤0.8% | ≤3.0% | report by visibility |
| Series-count exact accuracy | ≥99% | ≥95% | ≥90% or ambiguous |
| Dash-gap recovery | ≥99% visible trajectory | ≥95% | ≥90% |
| False grid/text inclusion | ≤0.2% curve length | ≤1.0% | ≤2.0% |

These are proposed engineering gates, not literature claims. Freeze them only after measuring a representative corpus.

### 24.8 Round-trip test

For every generated chart:

```text
numeric source
  → rendered SVG/PNG
  → digitized numeric series
  → rerendered overlay
```

Measure numeric and pixel errors. For generated GSS SVG, also parse embedded metadata and verify exact data recovery without rasterization.

### 24.9 Fuzzing

Fuzz:

- CSV delimiter/quote/encoding edge cases;
- workbook archives and XML limits;
- PNG chunks and dimensions through existing bounded decoder;
- SDN configurations;
- degenerate histograms;
- template-bank generation;
- correction-manifest operations;
- SVG escaping and metadata;
- optimizer constraints and NaN propagation.

---

## 25. Implementation plan

### Phase 0 — Freeze contracts and fixtures

**Goal:** establish terminology, data schemas, independent truth generators, and repository ownership before algorithms are added.

Tasks:

1. Add this design under the repository documentation hierarchy after link/lint review.
2. Define `NumericDataset`, histogram, provenance, error, and configuration schemas.
3. Freeze SDN schema version 1 and JSON interoperability schema.
4. Build small exact synthetic fixtures for 1, 2, 4, 16, 1+2+4+16, equal portions, and one unknown group.
5. Add repository audit script checking expected reusable owners still exist.
6. Decide common SVG helper extraction from office chart code.
7. Record independent development-oracle scripts outside production dependency paths.

**Exit gates:** schema round trip, source/config hashes, exact fixture generation, no ambiguous use of the word `group` in public fields.

### Phase 1 — Numeric ingestion and foundational math

**Goal:** analyze clean numeric data without image or NAND specialization.

Tasks:

1. CSV/TSV adapters for wide, long, histogram, and raw-sample forms.
2. Office `Sheet` adapter for XLSX/ODS and explicit ranges.
3. Validation, missing-value policy, unit metadata, and irregular-grid handling.
4. Stable streaming/weighted statistics and log-sum-exp.
5. Gaussian PDF, CDF, log-PDF, tail, and bin-integrated mass.
6. Noise models and baseline interfaces.
7. NNLS/simplex solver with KKT diagnostics.
8. Trust-region bounded optimizer reference.
9. Deterministic RNG streams.

**Exit gates:** differential numerical tests, histogram likelihood oracle tests, exact no-noise Gaussian recovery, typed errors for every invalid input class.

### Phase 2 — Scale significance and GSS

**Goal:** produce the FFT-like structured spectrum and candidate tables.

Tasks:

1. Gaussian kernels and derivative-of-Gaussian filters.
2. SiZer-like confidence map and ridge linking.
3. Template-bank types and default nine-variation policies.
4. Direct CPU correlation reference.
5. Matched response, analytical amplitude, Gaussian LLR, Poisson deviance response.
6. GSS tensor, flattening, peak clustering, raw/unique distinction.
7. GSS SDN/CSV/GraphText output.
8. SVG spectrum and position heatmap with embedded metadata.
9. Optional tensor FFT provider using the current runtime interface.

**Exit gates:** direct/FFT parity, all default templates distinct, known synthetic peaks localized, generated SVG metadata equals numeric output.

### Phase 3 — ASMD deterministic structured fitting

**Goal:** robustly fit all known quantity combinations plus unknown residual.

Tasks:

1. Parent/child model and rigid templates.
2. Variable-projection solver using NNLS/Poisson amplitude subproblems.
3. Exhaustive 16-mask search.
4. Semi-rigid deviations and regularization.
5. Flexible model constraints and label canonicalization.
6. Positive-spline or small flexible unknown component.
7. Multistart/global seeding from GSS.
8. model scores, profile likelihood, coherence, condition diagnostics.
9. equal-portion constrained fits.
10. reconstruction/residual/component SVGs.

**Exit gates:** recover worst-case equal 2/4/16 portions over a predefined overlap/SNR grid; unexpected groups produce unknown mass; non-identifiable cases are flagged.

### Phase 4 — Statistical verification

**Goal:** make `confidence` and `reference` modes scientifically defensible.

Tasks:

1. Parametric-bootstrap presence and equality tests.
2. Complete-search bootstrap for look-elsewhere calibration.
3. Student-t and Normal-Laplace atom families.
4. Flexible Bayesian challenge mixture with non-local/repulsive prior policy.
5. posterior model probabilities/evidence for finalist models.
6. posterior-predictive simulation and test statistics.
7. sensitivity report for noise, baseline, atom family, and prior/regularization.
8. ambiguity resolver and conflict representation.

**Exit gates:** calibrated false-positive/coverage campaigns, family-mismatch detection, final reports preserve conflicts.

### Phase 5 — NAND profile

**Goal:** support threshold-voltage data and NAND-specific outputs without conflating state count and group quantity.

Tasks:

1. SLC/MLC/TLC/QLC profiles and configurable logical mapping.
2. read-retry cumulative-to-histogram conversion with uncertainty.
3. state ordering and boundary calculation.
4. overlap, valley, tail, RBER, and reference-voltage metrics.
5. P/E, retention, temperature, layer, wordline condition metadata.
6. hierarchical multi-condition fitting.
7. emulator-based deterministic fixtures and independent hidden-truth separation.
8. NAND GraphText and report tables.

**Exit gates:** 2/4/8/16 physical state tests; read-retry round trip; known drift/widening recovered with intervals; TLC is not rejected by default 1/2/4/16 structured search.

### Phase 6 — Deterministic image digitizer

**Goal:** convert colored line charts to numeric series using auditable Simple algorithms.

Tasks:

1. canonical raster adapter over existing PNG ingest.
2. edge/segment/connected-component primitives.
3. plot-region, axis, tick, and grid hypotheses.
4. manual/no-text providers and calibration manifest.
5. sRGB/linear/XYZ/Lab conversion and color likelihood clusters.
6. text-like/decorative component classification.
7. solid-line dynamic-programming trace.
8. dashed/dotted hidden-state gap model.
9. crossing resolution and multi-hypothesis output.
10. numeric mapping and uncertainty propagation.
11. render-back overlay and metrics.
12. correction-manifest replay.

**Exit gates:** synthetic chart corpus targets; long straight colored/dashed data lines are retained; grid/text false inclusion is measured; ambiguous axes require correction rather than fabricated values.

### Phase 7 — OCR and learned providers

**Goal:** improve automatic extraction while preserving reference behavior and auditable fallbacks.

Tasks:

1. typed OCR SFFI provider with bounded input/output.
2. platform OCR adapters where useful.
3. optional learned instance-segmentation provider.
4. optional VLM legend association provider.
5. synthetic chart-training corpus export.
6. provider confidence calibration and render-back gating.
7. deterministic fallback and manual correction UX.

**Exit gates:** provider absence does not break pixel-coordinate extraction; semantic labels never override geometric inconsistency; provider versions and model hashes are recorded.

### Phase 8 — Unified CLI, plots, LLM tooling, and storage

**Goal:** one coherent workflow for files, interactive tools, and LLM agents.

Tasks:

1. `simple dist` and `simple chart digitize` commands.
2. SDN/JSON/CSV/GraphText writers.
3. all requested SVG/PNG outputs.
4. output manifests and stable filenames.
5. database import/export tables.
6. named retrieval vectors and exact reranking API.
7. optional Arrow/Parquet provider.
8. LLM tool schema that returns compact text plus artifact references.
9. GUI/IDE/office integration through the same command contracts.

**Exit gates:** end-to-end source reproducibility; token-bounded GraphText; no LLM path depends solely on raster reading; database search can explain matched dimensions.

### Phase 9 — Hardening and release

Tasks:

1. corpus-wide statistical calibration.
2. backend parity and performance characterization without weakening reference algorithms.
3. fuzzing and untrusted-file limits.
4. API/spec/doc synchronization.
5. migration/versioning tests for stored results.
6. reproducible release corpus and golden artifact bundle.
7. license review for optional OCR/ML models and datasets.
8. documented failure taxonomy and operator guide.

**Release gate:** no P0/P1 correctness gaps; all known non-identifiable fixtures report uncertainty; complete raw/config/model provenance; no mock provider accepted as production evidence.

---

## 26. Parallel workstream plan

After Phase 0 contracts are frozen, use parallel lanes with explicit owners.

| Lane | Ownership | Can start after | Must not modify |
|---|---|---|---|
| A | stable math, atoms, integration, NNLS | Phase 0 | chart/NAND policy |
| B | GSS and scale significance | core types + Gaussian atom | office codecs |
| C | ASMD/VarPro/statistics | NNLS + GSS types | image ingest |
| D | tabular adapters | core dataset types | workbook internals except narrow adapter |
| E | chart geometry/color tracing | raster types | ASMD internals |
| F | NAND profile | ASMD model interfaces | emulator physics behavior |
| G | plots/GraphText/storage | result schemas | fitting algorithms |
| H | optional providers | provider contracts | reference semantics |
| V | independent verification/tests | fixture contracts | production algorithms except test hooks |

Integration rules:

- Every lane adds specs with its API change.
- Shared type changes require a small dedicated commit before dependent logic.
- Provider work cannot land before reference tests exist.
- Generated artifact formats require schema-version updates and migration tests.
- Statistical oracle tests are reviewed independently from fitting code.

---

## 27. Acceptance criteria

### 27.1 Functional

- One command accepts CSV, XLSX/ODS, or PNG and produces the same canonical `NumericDataset` when inputs encode the same data within digitization error.
- GSS emits nine default variations per configured quantity and arbitrary custom banks.
- GSS graph peaks include exact machine-readable metadata.
- ASMD can fit all simultaneous known groups and arbitrary nonnegative portions.
- Equal parent portions are tested directly.
- An unknown group is not silently mapped into 1/2/4/16.
- NAND mode supports 2, 4, 8, and 16 physical states.
- Image mode extracts multiple colored solid/dashed/dotted lines and outputs numeric lists.
- Letters, legends, axes, and grid lines are classified and visible in diagnostics.
- Manual corrections replay exactly.
- LLM output includes exact numbers, uncertainty, warnings, and provenance.

### 27.2 Scientific

- Raw observations remain immutable and are used by default for fitting.
- Every model choice exposes likelihood/evidence and residual diagnostics.
- Bootstrap search repeats candidate/model selection.
- Parent existence and child resolution are reported separately.
- Non-identifiable cases are not labeled confirmed.
- Heavy-tail/skew alternatives are checked before interpreting extra Gaussian groups.
- Posterior-predictive failure prevents an unconditional “model accepted” result.

### 27.3 Engineering

- Pure-Simple reference path has no required Python/R dependency.
- Optional SFFI/GPU providers fail closed and expose versions.
- Existing PNG, office, FFT, statistics, science-math, NAND-emulator, and chart code is reused or generalized rather than copied.
- Stored results are schema-versioned and reproducible from source/config hashes.
- Untrusted input limits and typed errors are tested.

---

## 28. Key risks and mitigations

| Risk | Consequence | Mitigation |
|---|---|---|
| Template nonorthogonality | 16 group leaks into 1/2/4 spectrum | joint ASMD, unique spectrum, coherence report |
| Severe overlap/non-identifiability | unstable portions | multi-condition fit, profile/posterior intervals, `NonIdentifiable` state |
| Heavy tails modeled as extra groups | false physical interpretation | Normal-Laplace/Student challenge, PPC tail checks |
| Unknown structure forced into known groups | biased portions | explicit `alpha_U U(x)` |
| Smoothing removes small group | false negative | analysis-only scale space; fit raw data |
| Search creates false bump | inflated significance | full-search parametric bootstrap |
| Image text/grid contamination | false components | explicit decoration masks, render-back validation |
| Straight dashed data line removed as grid | data loss | combined color/legend/dash role score, not orientation alone |
| Same-color crossings | trajectory swaps | style/tangent/global min-cost assignment, retain alternatives |
| OCR tick error | wrong numeric scale | robust calibration, residuals, multiple hypotheses/manual ticks |
| Log axis mistaken for linear | globally wrong data | compare calibration models and tick semantics |
| XLSX formula/external link behavior | unsafe/wrong values | no formula execution, record cached-value use, block external fetch |
| Local optimizer | wrong decomposition | exhaustive masks, multistart, global seeds, retained local modes |
| Bayesian prior dominates weak data | misleading certainty | sensitivity analysis and challenge priors |
| GPU/provider drift | inconsistent results | reference parity corpus and typed capability fallback |
| Repository duplication | maintenance debt | strict owner modules and reuse audit |

---

## 29. Decisions that should be frozen before coding

1. **Names:** retain project-defined `GSS` and `ASMD`, or select longer public names.
2. **Primary package path:** `std.common.science_distribution` versus a shorter `std.science.dist` after naming-harmony review.
3. **Canonical on-disk format:** SDN metadata + binary f64 vectors for v1; Arrow/Parquet provider timing.
4. **NAND interpretation:** exact semantics of the user’s 1/2/4/16 group templates and canonical child positions/weights.
5. **Default nominal widths/spacings:** global normalized defaults versus a calibration/profile table per data source.
6. **Unknown component:** positive spline, small flexible mixture, or both.
7. **Bayesian engine:** pure-Simple SMC/nested-sampling target versus an initial validated SFFI provider.
8. **OCR provider:** which platform/library is legally and operationally acceptable.
9. **Generated plot owner:** extract from office chart now or add a small common SVG module first.
10. **Statistical policy thresholds:** define only after calibration corpus results.

Items 4 and 5 require real representative NAND datasets or synthetic specifications. Until then, the architecture supports configurable templates and must not claim a universal physical layout.

---

## 30. Recommended first vertical slice

Build one end-to-end, correctness-focused slice before implementing every optional family:

```text
CSV or PNG
  → one NumericSeries
  → Gaussian noise/Poisson count model
  → analysis-only scale space
  → GSS [1,2,4,16], default 9 variants
  → rigid Gaussian ASMD + unknown positive spline
  → exhaustive masks + VarPro
  → 256/1000 replicate bootstrap
  → SVG + SDN + CSV + GraphText
```

Image scope for the slice:

- one linear-x/linear-y plot;
- white background;
- multiple distinct colored lines;
- solid and dashed styles;
- grid and labels;
- manual tick fallback;
- render-back overlay.

NAND scope:

- QLC 16-state numeric fixture;
- TLC 8-state regression showing state-count independence;
- combined 1+2+4+16 structured fixture with equal 2/4/16 parent portions;
- P/E widening/shift fixture from the current emulator.

This slice exercises every architectural boundary without waiting for a complete OCR or Bayesian implementation.

---

## 31. End-to-end reference pseudocode

```simple
fn analyze_source_reference(
    source: AnalysisSource,
    cfg: DistributionAnalysisConfig
) -> Result<DistributionAnalysisBundle, AnalysisError>:
    # A. Ingest; image paths are digitized before numeric analysis.
    val ingested = match source:
        AnalysisSource.Image(bytes):
            val image = decode_raster_bounded(bytes, cfg.ingest.image_limits)?
            val chart = digitize_chart(image, cfg.digitize)?
            IngestedAnalysisSource(
                dataset: digitized_chart_to_dataset(chart)?,
                digitization: chart
            )
        _:
            IngestedAnalysisSource(
                dataset: load_numeric_dataset(source, cfg.ingest)?,
                digitization: nil
            )

    validate_dataset(ingested.dataset)?

    var scale_results: [ScaleSignificance] = []
    var gss_results: [GssSpectrum] = []
    var asmd_results: [AsmdResult] = []

    # B. Each visible/numeric series is analyzed, optionally with a joint model.
    for series in ingested.dataset.series:
        val noise = fit_noise_model_for_series(series, cfg.preprocess.noise)?
        val scale = compute_scale_significance_raw(series, noise, cfg.scale_space)?
        val bank = build_gss_bank(cfg.gss.template_policy)?
        val gss = gss_transform_raw(series, bank, noise, cfg.gss)?
        val fit = asmd_reference_fit_series(series, scale, gss, noise, cfg.asmd)?

        scale_results.push(scale)
        gss_results.push(gss)
        asmd_results.push(fit)

    # C. Optional joint repeated-condition and NAND interpretation.
    val nand_result = if cfg.nand != nil:
        analyze_nand_distribution_joint(
            ingested.dataset,
            asmd_results,
            cfg.nand
        )?
    else:
        nil

    # D. Cross-series conflicts, digitization diagnostics, and reproducibility.
    val diagnostics = resolve_analysis_diagnostics(
        ingested,
        scale_results,
        gss_results,
        asmd_results,
        nand_result,
        cfg
    )

    var bundle = DistributionAnalysisBundle(
        dataset: ingested.dataset,
        digitization: ingested.digitization,
        scale_significance: scale_results,
        gss: gss_results,
        asmd: asmd_results,
        nand: nand_result,
        diagnostics: diagnostics,
        artifacts: [],
        provenance: build_provenance(source, cfg)
    )

    bundle.artifacts = render_analysis_bundle(bundle, cfg.output)?
    Ok(bundle)
```

---

## 32. Research references

### NAND threshold-voltage distributions

1. Yu Cai, Erich F. Haratsch, Onur Mutlu, and Ken Mai, **“Threshold Voltage Distribution in MLC NAND Flash Memory: Characterization, Analysis, and Modeling,”** DATE 2013. DOI: `10.7873/DATE.2013.266`. Public PDF: <https://www.pdl.cmu.edu/PDL-FTP/NVM/flash-memory-voltage-characterization_date13.pdf>
2. Yixin Luo et al., **“Improving 3D NAND Flash Memory Lifetime by Tolerating Early Retention Loss and Process Variation,”** Proceedings of the ACM on Measurement and Analysis of Computing Systems, 2018. DOI: `10.1145/3224432`.
3. Wen Liu et al., **“Modeling of Threshold Voltage Distribution in 3D NAND Flash Memory,”** DATE 2021. DOI: `10.23919/DATE51398.2021.9473974`.
4. T. Parnell et al., **“Modelling of the Threshold Voltage Distributions of Sub-20nm NAND Flash Memory,”** GLOBECOM 2014. DOI: `10.1109/GLOCOM.2014.7037159`.
5. Ziwei Liu, Yi Liu, and Paul H. Siegel, **“Generative Modeling of NAND Flash Memory Voltage Level Distributions,”** NVMW 2021: <https://nvmw.ucsd.edu/nvmw2021-program/nvmw2021-data/nvmw2021-paper72-final_version_your_extended_abstract.pdf>
6. Yu Cai, Saugata Ghose, Erich F. Haratsch, Yixin Luo, and Onur Mutlu, **“Errors in Flash-Memory-Based Solid-State Drives: Analysis, Mitigation, and Recovery,”** <https://arxiv.org/abs/1711.11427>

### Scale-space, structured matching, and fitting

7. Probal Chaudhuri and J. S. Marron, **“SiZer for Exploration of Structures in Curves,”** JASA 94(447), 1999. DOI: `10.1080/01621459.1999.10474186`.
8. Tony Lindeberg, **“Feature Detection with Automatic Scale Selection,”** International Journal of Computer Vision, 1998.
9. Stéphane Mallat and Zhifeng Zhang, **“Matching Pursuits with Time-Frequency Dictionaries,”** IEEE Transactions on Signal Processing 41(12), 1993. DOI: `10.1109/78.258082`.
10. Dianne P. O’Leary and Bert W. Rust, **“Variable Projection for Nonlinear Least Squares Problems,”** Computational Optimization and Applications 54, 2013. DOI: `10.1007/s10589-012-9492-9`. NIST summary: <https://www.nist.gov/publications/variable-projection-nonlinear-least-squares-problems>
11. Z. D. Feng and C. E. McCulloch, **“Using Bootstrap Likelihood Ratios in Finite Mixture Models,”** JRSS B 58(3), 1996: <https://academic.oup.com/jrsssb/article/58/3/609/7027915>
12. Jairo Fúquene, Mark Steel, and David Rossell, **“On Choosing Mixture Components via Non-Local Priors,”** JRSS B, 2019; preprint: <https://arxiv.org/abs/1604.00314>

### Chart digitization and chart-to-data

13. Junyu Luo et al., **“ChartOCR: Data Extraction From Charts Images via a Deep Hybrid Framework,”** WACV 2021: <https://openaccess.thecvf.com/content/WACV2021/html/Luo_ChartOCR_Data_Extraction_From_Charts_Images_via_a_Deep_Hybrid_WACV_2021_paper.html>
14. Hajime Kato et al., **“Parsing Line Chart Images Using Linear Programming,”** WACV 2022: <https://openaccess.thecvf.com/content/WACV2022/html/Kato_Parsing_Line_Chart_Images_Using_Linear_Programming_WACV_2022_paper.html>
15. Weixin Jiang et al., **“Plot2Spectra: an Automatic Spectra Extraction Tool,”** Digital Discovery 1, 719–731, 2022. DOI: `10.1039/D1DD00036E`; preprint: <https://arxiv.org/abs/2107.02827>
16. Md. Yousuf Hassan et al., **“LineEX: Data Extraction From Scientific Line Charts,”** WACV 2023: <https://openaccess.thecvf.com/content/WACV2023/html/P._LineEX_Data_Extraction_From_Scientific_Line_Charts_WACV_2023_paper.html>
17. Md Touhidul Islam et al., **“ChartZero: Synthetic Priors Enable Zero Shot Chart Data Extraction,”** 2026: <https://arxiv.org/abs/2605.05820>
18. Fangyu Liu et al., **“DePlot: One-shot Visual Language Reasoning by Plot-to-Table Translation,”** <https://arxiv.org/abs/2212.10505>

### Columnar representation

19. Apache Arrow, **Columnar Format Specification**: <https://arrow.apache.org/docs/format/Columnar.html>
20. Apache Arrow, **Arrow and Parquet FAQ**: <https://arrow.apache.org/faq/>
21. Apache Parquet documentation through Arrow: <https://arrow.apache.org/docs/python/parquet.html>

---

## 33. Final recommendation

Implement **GSS + ASMD as one distribution-analysis subsystem**, fronted by a reusable numeric/image ingestion layer and backed by independent statistical verification.

The central design rules are:

1. Preserve raw observations and provenance.
2. Treat GSS as an FFT-like candidate/evidence view, not an orthogonal decomposition.
3. Estimate top-level portions jointly; never infer group importance from child peak height.
4. Keep NAND physical state count separate from structured group quantity.
5. Include an unknown residual and report conflicts rather than force expected groups.
6. Use scale significance, flexible challenge models, bootstrap calibration, and posterior-predictive checks in `reference` mode.
7. Digitize images through visible geometry, calibration, uncertainty, and render-back validation.
8. Give LLMs exact numeric text and embedded SVG metadata rather than requiring pixel estimation.
9. Implement the reference pipeline in Simple; optional OCR, ML, FFT, Bayesian, GPU, and Parquet providers must not redefine correctness.

This produces a tool that can answer both:

> “Which 1/2/4/16 structures match this graph, and where are the high spectrum peaks?”

and the more important question:

> “After accounting for overlap, noise, tails, image-extraction uncertainty, and alternative models, what portions of the data are credibly attributable to each structured group, and what remains unresolved?”

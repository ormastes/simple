# CUDA Font Atlas Launch Arguments Specification

> Manually synchronized on 2026-07-12; no Simple/docgen or CUDA device command
> ran in this session.

The scenario allocates value and pointer tables and checks all 15 ordered
eight-byte slots: atlas/destination handles, atlas dimensions/count/offset,
quad dimensions, destination dimensions/count/offset, and color. It includes
negative destination coordinates and a high-bit ARGB value.

Source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_launch_args_spec.spl`


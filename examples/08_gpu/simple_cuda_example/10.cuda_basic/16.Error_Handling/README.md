# 16. Error Handling - Result<T, GpuError> Patterns

## Concept

Simple uses `Result<T, GpuError>` instead of C/CUDA's `cudaError_t` error codes.
The `?` operator propagates errors automatically, eliminating the need for manual
status checks after every API call.

## C/CUDA vs Simple

### C/CUDA - manual error checking
```c
cudaError_t err;
float *d_a;
err = cudaMalloc(&d_a, n * sizeof(float));
if (err != cudaSuccess) {
    fprintf(stderr, "cudaMalloc failed: %s\n", cudaGetErrorString(err));
    return err;
}
err = cudaMemcpy(d_a, h_a, n * sizeof(float), cudaMemcpyHostToDevice);
if (err != cudaSuccess) {
    cudaFree(d_a);
    fprintf(stderr, "cudaMemcpy failed: %s\n", cudaGetErrorString(err));
    return err;
}
```

### Simple - Result + ? operator
```simple
fn upload_data(data: [f32]) -> Result<GpuPtr, GpuError>:
    val d_a = gpu_alloc(data.len() * 4)?     # ? propagates on error
    gpu_upload_f32(d_a, data)?                # ? propagates on error
    Ok(d_a)
```

## Error Handling Patterns

| Pattern                | Description                                    |
|------------------------|------------------------------------------------|
| `gpu_alloc(n)?`        | Propagate error to caller                      |
| `match result:`        | Handle Ok/Err explicitly                       |
| `result ?? default`    | Provide fallback value on error                |
| `Result<T, GpuError>`  | Return type for fallible GPU functions          |

## Run
```bash
bin/simple examples/simple_cuda_example/10.cuda_basic/16.Error_Handling/main.spl
```

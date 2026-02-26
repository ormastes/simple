// PyTorch CUDA tests to verify GPU acceleration works
// These tests only run when pytorch feature is enabled AND CUDA is available

#[test]
#[cfg(feature = "pytorch")]
fn test_cuda_availability() {
    use simple_runtime::value::torch::*;

    let cuda_available = rt_torch_cuda_available();
    let device_count = rt_torch_cuda_device_count();

    println!("CUDA available: {}", cuda_available != 0);
    println!("CUDA device count: {}", device_count);

    // This test always passes but prints CUDA info
    assert!(true);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cpu_tensor_creation() {
    use simple_runtime::value::torch::*;

    // Explicitly create tensor on CPU (device=0)
    let shape = vec![2i64, 3];
    let handle = unsafe { rt_torch_zeros(shape.as_ptr(), shape.len() as i32, 0, 0) };
    assert_ne!(handle, 0, "CPU tensor creation should succeed");

    rt_torch_free(handle);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cuda_tensor_creation() {
    use simple_runtime::value::torch::*;

    // Check if CUDA is available
    if rt_torch_cuda_available() == 0 {
        println!("CUDA not available, skipping test");
        return;
    }

    // Create tensor on CUDA:0 (device=1)
    let shape = vec![2i64, 3];
    let handle = unsafe { rt_torch_zeros(shape.as_ptr(), shape.len() as i32, 0, 1) };
    assert_ne!(handle, 0, "CUDA tensor creation should succeed");

    rt_torch_free(handle);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cuda_operations() {
    use simple_runtime::value::torch::*;

    // Check if CUDA is available
    if rt_torch_cuda_available() == 0 {
        println!("CUDA not available, skipping test");
        return;
    }

    // Create tensors on CUDA
    let shape = vec![4i64, 4];
    let a = unsafe { rt_torch_ones(shape.as_ptr(), shape.len() as i32, 0, 1) }; // CUDA:0
    let b = unsafe { rt_torch_ones(shape.as_ptr(), shape.len() as i32, 0, 1) }; // CUDA:0

    assert_ne!(a, 0, "First CUDA tensor creation should succeed");
    assert_ne!(b, 0, "Second CUDA tensor creation should succeed");

    // Test addition on CUDA
    let c = rt_torch_add(a, b);
    assert_ne!(c, 0, "CUDA tensor addition should succeed");

    // Clean up
    rt_torch_free(a);
    rt_torch_free(b);
    rt_torch_free(c);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cuda_matmul() {
    use simple_runtime::value::torch::*;

    // Check if CUDA is available
    if rt_torch_cuda_available() == 0 {
        println!("CUDA not available, skipping test");
        return;
    }

    // Create matrices on CUDA
    let shape_a = vec![128i64, 256];
    let shape_b = vec![256i64, 512];

    let a = unsafe { rt_torch_randn(shape_a.as_ptr(), shape_a.len() as i32, 0, 1) };
    let b = unsafe { rt_torch_randn(shape_b.as_ptr(), shape_b.len() as i32, 0, 1) };

    assert_ne!(a, 0, "First CUDA matrix creation should succeed");
    assert_ne!(b, 0, "Second CUDA matrix creation should succeed");

    // Matrix multiply on CUDA
    let c = rt_torch_matmul(a, b);
    assert_ne!(c, 0, "CUDA matrix multiply should succeed");

    // Verify shape
    let mut shape_buf = [0i64; 8];
    let ndim = unsafe { rt_torch_shape(c, shape_buf.as_mut_ptr(), 8) };
    assert_eq!(ndim, 2, "Result should be 2D");
    assert_eq!(shape_buf[0], 128, "First dimension should be 128");
    assert_eq!(shape_buf[1], 512, "Second dimension should be 512");

    // Clean up
    rt_torch_free(a);
    rt_torch_free(b);
    rt_torch_free(c);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cuda_activations() {
    use simple_runtime::value::torch::*;

    // Check if CUDA is available
    if rt_torch_cuda_available() == 0 {
        println!("CUDA not available, skipping test");
        return;
    }

    // Create tensor on CUDA
    let shape = vec![64i64, 64];
    let tensor = unsafe { rt_torch_randn(shape.as_ptr(), shape.len() as i32, 0, 1) };
    assert_ne!(tensor, 0, "CUDA tensor creation should succeed");

    // Test activations on CUDA
    let mish = rt_torch_mish(tensor);
    assert_ne!(mish, 0, "CUDA Mish should succeed");

    let elu = rt_torch_elu(tensor, 1.0);
    assert_ne!(elu, 0, "CUDA ELU should succeed");

    let softplus = rt_torch_softplus(tensor, 1.0, 20.0);
    assert_ne!(softplus, 0, "CUDA Softplus should succeed");

    let leaky_relu = rt_torch_leaky_relu(tensor, 0.01);
    assert_ne!(leaky_relu, 0, "CUDA LeakyReLU should succeed");

    // Clean up
    rt_torch_free(tensor);
    rt_torch_free(mish);
    rt_torch_free(elu);
    rt_torch_free(softplus);
    rt_torch_free(leaky_relu);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_cpu_to_cuda_transfer() {
    use simple_runtime::value::torch::*;

    // Check if CUDA is available
    if rt_torch_cuda_available() == 0 {
        println!("CUDA not available, skipping test");
        return;
    }

    // Create tensor on CPU
    let shape = vec![10i64, 10];
    let cpu_tensor = unsafe { rt_torch_randn(shape.as_ptr(), shape.len() as i32, 0, 0) };
    assert_ne!(cpu_tensor, 0, "CPU tensor creation should succeed");

    // Transfer to CUDA
    let cuda_tensor = rt_torch_to_cuda(cpu_tensor, 0);
    assert_ne!(cuda_tensor, 0, "CPU to CUDA transfer should succeed");

    // Transfer back to CPU
    let cpu_tensor2 = rt_torch_to_cpu(cuda_tensor);
    assert_ne!(cpu_tensor2, 0, "CUDA to CPU transfer should succeed");

    // Clean up
    rt_torch_free(cpu_tensor);
    rt_torch_free(cuda_tensor);
    rt_torch_free(cpu_tensor2);
}

#[test]
#[cfg(not(feature = "pytorch"))]
fn pytorch_cuda_feature_disabled() {
    assert!(true, "PyTorch feature is disabled");
}

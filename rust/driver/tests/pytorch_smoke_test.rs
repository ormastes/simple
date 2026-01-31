// PyTorch smoke tests to verify libtorch integration works
// Tests are conditionally compiled based on pytorch feature flag

#[test]
#[cfg(feature = "pytorch")]
fn test_tensor_creation() {
    use simple_runtime::value::torch::*;

    // Test basic tensor creation
    let shape = vec![2i64, 3];
    let handle = unsafe { rt_torch_zeros(shape.as_ptr(), shape.len() as i32, 0, 0) };
    assert_ne!(handle, 0, "Tensor creation should succeed");

    // Clean up
    rt_torch_free(handle);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_tensor_operations() {
    use simple_runtime::value::torch::*;

    // Create two tensors
    let shape = vec![2i64, 2];
    let a = unsafe { rt_torch_ones(shape.as_ptr(), shape.len() as i32, 0, 0) };
    let b = unsafe { rt_torch_ones(shape.as_ptr(), shape.len() as i32, 0, 0) };

    assert_ne!(a, 0, "First tensor creation should succeed");
    assert_ne!(b, 0, "Second tensor creation should succeed");

    // Test addition
    let c = rt_torch_add(a, b);
    assert_ne!(c, 0, "Tensor addition should succeed");

    // Clean up
    rt_torch_free(a);
    rt_torch_free(b);
    rt_torch_free(c);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_activation_functions() {
    use simple_runtime::value::torch::*;

    // Test basic activations
    let shape = vec![3i64, 3];
    let tensor = unsafe { rt_torch_randn(shape.as_ptr(), shape.len() as i32, 0, 0) };
    assert_ne!(tensor, 0, "Tensor creation should succeed");

    // Test ReLU
    let relu_result = rt_torch_relu(tensor);
    assert_ne!(relu_result, 0, "ReLU should succeed");

    // Test GELU
    let gelu_result = rt_torch_gelu(tensor);
    assert_ne!(gelu_result, 0, "GELU should succeed");

    // Test SiLU
    let silu_result = rt_torch_silu(tensor);
    assert_ne!(silu_result, 0, "SiLU should succeed");

    // Clean up
    rt_torch_free(tensor);
    rt_torch_free(relu_result);
    rt_torch_free(gelu_result);
    rt_torch_free(silu_result);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_new_activation_functions() {
    use simple_runtime::value::torch::*;

    // Test newly added activation functions
    let shape = vec![4i64, 4];
    let tensor = unsafe { rt_torch_randn(shape.as_ptr(), shape.len() as i32, 0, 0) };
    assert_ne!(tensor, 0, "Tensor creation should succeed");

    // Test Mish
    let mish_result = rt_torch_mish(tensor);
    assert_ne!(mish_result, 0, "Mish should succeed");

    // Test ELU with alpha=1.0
    let elu_result = rt_torch_elu(tensor, 1.0);
    assert_ne!(elu_result, 0, "ELU should succeed");

    // Test Softplus with beta=1.0, threshold=20.0
    let softplus_result = rt_torch_softplus(tensor, 1.0, 20.0);
    assert_ne!(softplus_result, 0, "Softplus should succeed");

    // Test LeakyReLU with slope=0.01
    let leaky_relu_result = rt_torch_leaky_relu(tensor, 0.01);
    assert_ne!(leaky_relu_result, 0, "LeakyReLU should succeed");

    // Clean up
    rt_torch_free(tensor);
    rt_torch_free(mish_result);
    rt_torch_free(elu_result);
    rt_torch_free(softplus_result);
    rt_torch_free(leaky_relu_result);
}

#[test]
#[cfg(feature = "pytorch")]
fn test_matrix_multiply() {
    use simple_runtime::value::torch::*;

    // Test matmul
    let shape_a = vec![4i64, 6];
    let shape_b = vec![6i64, 8];

    let a = unsafe { rt_torch_zeros(shape_a.as_ptr(), shape_a.len() as i32, 0, 0) };
    let b = unsafe { rt_torch_zeros(shape_b.as_ptr(), shape_b.len() as i32, 0, 0) };

    assert_ne!(a, 0, "First matrix creation should succeed");
    assert_ne!(b, 0, "Second matrix creation should succeed");

    let c = rt_torch_matmul(a, b);
    assert_ne!(c, 0, "Matrix multiply should succeed");

    // Verify shape is [4, 8]
    let mut shape_buf = [0i64; 8];
    let ndim = unsafe { rt_torch_shape(c, shape_buf.as_mut_ptr(), 8) };
    assert_eq!(ndim, 2, "Result should be 2D");
    assert_eq!(shape_buf[0], 4, "First dimension should be 4");
    assert_eq!(shape_buf[1], 8, "Second dimension should be 8");

    // Clean up
    rt_torch_free(a);
    rt_torch_free(b);
    rt_torch_free(c);
}

#[test]
#[cfg(not(feature = "pytorch"))]
fn pytorch_feature_disabled() {
    // This test runs when pytorch feature is NOT enabled
    // Just to show that tests work in both configurations
    assert!(true, "PyTorch feature is disabled");
}

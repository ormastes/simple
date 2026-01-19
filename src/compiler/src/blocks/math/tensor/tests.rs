//! Tests for tensor operations.

use super::core::Tensor;

#[test]
fn test_tensor_creation() {
    let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
    assert_eq!(t.shape, vec![2, 2]);
    assert_eq!(t.data, vec![1.0, 2.0, 3.0, 4.0]);
}

#[test]
fn test_zeros() {
    let t = Tensor::zeros(vec![2, 3]);
    assert_eq!(t.shape, vec![2, 3]);
    assert_eq!(t.data, vec![0.0; 6]);
}

#[test]
fn test_ones() {
    let t = Tensor::ones(vec![2, 2]);
    assert_eq!(t.data, vec![1.0; 4]);
}

#[test]
fn test_eye() {
    let t = Tensor::eye(3);
    assert_eq!(t.shape, vec![3, 3]);
    assert_eq!(t.data, vec![1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0]);
}

#[test]
fn test_arange() {
    let t = Tensor::arange(0.0, 5.0, 1.0);
    assert_eq!(t.data, vec![0.0, 1.0, 2.0, 3.0, 4.0]);
}

#[test]
fn test_linspace() {
    let t = Tensor::linspace(0.0, 1.0, 5);
    assert_eq!(t.shape, vec![5]);
    assert!((t.data[0] - 0.0).abs() < 1e-10);
    assert!((t.data[4] - 1.0).abs() < 1e-10);
}

#[test]
fn test_add() {
    let a = Tensor::new(vec![1.0, 2.0], vec![2]).unwrap();
    let b = Tensor::new(vec![3.0, 4.0], vec![2]).unwrap();
    let c = a.add(&b).unwrap();
    assert_eq!(c.data, vec![4.0, 6.0]);
}

#[test]
fn test_broadcast_add() {
    let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
    let b = Tensor::new(vec![10.0, 20.0], vec![2]).unwrap();
    let c = a.add(&b).unwrap();
    assert_eq!(c.shape, vec![2, 2]);
    assert_eq!(c.data, vec![11.0, 22.0, 13.0, 24.0]);
}

#[test]
fn test_matmul() {
    let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
    let b = Tensor::new(vec![5.0, 6.0, 7.0, 8.0], vec![2, 2]).unwrap();
    let c = a.matmul(&b).unwrap();
    assert_eq!(c.shape, vec![2, 2]);
    // [1,2] @ [5,6] = [1*5+2*7, 1*6+2*8] = [19, 22]
    // [3,4]   [7,8]   [3*5+4*7, 3*6+4*8] = [43, 50]
    assert_eq!(c.data, vec![19.0, 22.0, 43.0, 50.0]);
}

#[test]
fn test_transpose() {
    let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0], vec![2, 3]).unwrap();
    let b = a.transpose().unwrap();
    assert_eq!(b.shape, vec![3, 2]);
    assert_eq!(b.data, vec![1.0, 4.0, 2.0, 5.0, 3.0, 6.0]);
}

#[test]
fn test_sum() {
    let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
    assert_eq!(t.sum(), 10.0);
}

#[test]
fn test_mean() {
    let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
    assert_eq!(t.mean(), 2.5);
}

#[test]
fn test_reshape() {
    let a = Tensor::arange(0.0, 6.0, 1.0);
    let b = a.reshape(vec![2, 3]).unwrap();
    assert_eq!(b.shape, vec![2, 3]);
}

#[test]
fn test_sigmoid() {
    let t = Tensor::new(vec![0.0], vec![1]).unwrap();
    let s = t.sigmoid();
    assert!((s.data[0] - 0.5).abs() < 1e-10);
}

#[test]
fn test_relu() {
    let t = Tensor::new(vec![-1.0, 0.0, 1.0, 2.0], vec![4]).unwrap();
    let r = t.relu();
    assert_eq!(r.data, vec![0.0, 0.0, 1.0, 2.0]);
}

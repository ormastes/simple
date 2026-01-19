//! Tensor creation, manipulation, and ML activation functions.
//!
//! Provides:
//! - Tensor creation (zeros, ones, eye, arange, linspace, rand, randn)
//! - Tensor operations (matmul, dot, transpose, reshape, flatten, squeeze, unsqueeze)
//! - Tensor properties (shape, ndim, numel, item)
//! - Tensor reductions (sum, mean, var, std, argmin, argmax)
//! - Activation functions (relu, sigmoid, softmax, tanh)

use super::super::tensor::Tensor;
use super::MathValue;
use crate::error::CompileError;

// ==========================================================================
// Helper Functions
// ==========================================================================

/// Convert args to shape vector
pub fn args_to_shape(args: &[MathValue]) -> Result<Vec<usize>, CompileError> {
    if args.len() == 1 {
        // Could be a single int or a tensor/array of ints
        match &args[0] {
            MathValue::Tensor(t) => {
                return Ok(t.data.iter().map(|&x| x as usize).collect());
            }
            _ => {}
        }
    }
    args.iter()
        .map(|a| {
            let v = a.as_f64()? as i64;
            if v < 0 {
                Err(CompileError::Semantic("shape dimensions must be non-negative".into()))
            } else {
                Ok(v as usize)
            }
        })
        .collect()
}

/// Require tensor arguments
pub fn require_tensor_args(name: &str, args: &[MathValue], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::Semantic(format!(
            "{} requires {} argument(s), got {}",
            name,
            expected,
            args.len()
        )));
    }
    Ok(())
}

/// Get tensor from MathValue, converting scalars
pub fn get_tensor(val: &MathValue) -> Result<Tensor, CompileError> {
    match val {
        MathValue::Tensor(t) => Ok(t.clone()),
        v => Ok(Tensor::scalar(v.as_f64()?)),
    }
}

// ==========================================================================
// Tensor Creation Functions
// ==========================================================================

pub fn eval_tensor(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("tensor requires 1 argument".into()));
    }
    match &args[0] {
        MathValue::Tensor(t) => Ok(MathValue::Tensor(t.clone())),
        _ => {
            let val = args[0].as_f64()?;
            Ok(MathValue::Tensor(Tensor::scalar(val)))
        }
    }
}

pub fn eval_zeros(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let shape = args_to_shape(args)?;
    Ok(MathValue::Tensor(Tensor::zeros(shape)))
}

pub fn eval_ones(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let shape = args_to_shape(args)?;
    Ok(MathValue::Tensor(Tensor::ones(shape)))
}

pub fn eval_full(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::Semantic("full requires shape and fill value".into()));
    }
    let fill = args.last().unwrap().as_f64()?;
    let shape = args_to_shape(&args[..args.len() - 1])?;
    Ok(MathValue::Tensor(Tensor::full(shape, fill)))
}

pub fn eval_eye(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("eye requires 1 argument".into()));
    }
    let n = args[0].as_f64()? as usize;
    Ok(MathValue::Tensor(Tensor::eye(n)))
}

pub fn eval_arange(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let (start, end, step) = match args.len() {
        1 => (0.0, args[0].as_f64()?, 1.0),
        2 => (args[0].as_f64()?, args[1].as_f64()?, 1.0),
        3 => (args[0].as_f64()?, args[1].as_f64()?, args[2].as_f64()?),
        _ => return Err(CompileError::Semantic("arange takes 1-3 arguments".into())),
    };
    Ok(MathValue::Tensor(Tensor::arange(start, end, step)))
}

pub fn eval_linspace(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::Semantic("linspace requires 3 arguments".into()));
    }
    let start = args[0].as_f64()?;
    let end = args[1].as_f64()?;
    let steps = args[2].as_f64()? as usize;
    Ok(MathValue::Tensor(Tensor::linspace(start, end, steps)))
}

pub fn eval_rand(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let shape = args_to_shape(args)?;
    Ok(MathValue::Tensor(Tensor::rand(shape)))
}

pub fn eval_randn(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let shape = args_to_shape(args)?;
    Ok(MathValue::Tensor(Tensor::randn(shape)))
}

// ==========================================================================
// Tensor Operations
// ==========================================================================

pub fn eval_matmul(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("matmul", args, 2)?;
    let a = get_tensor(&args[0])?;
    let b = get_tensor(&args[1])?;
    Ok(MathValue::Tensor(a.matmul(&b)?))
}

pub fn eval_dot(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("dot", args, 2)?;
    let a = get_tensor(&args[0])?;
    let b = get_tensor(&args[1])?;
    Ok(MathValue::Float(a.dot(&b)?))
}

pub fn eval_transpose(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("transpose", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Tensor(t.transpose()?))
}

pub fn eval_reshape(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::Semantic("reshape requires tensor and shape".into()));
    }
    let t = get_tensor(&args[0])?;
    let shape = args_to_shape(&args[1..])?;
    Ok(MathValue::Tensor(t.reshape(shape)?))
}

pub fn eval_flatten(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("flatten", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Tensor(t.flatten()))
}

pub fn eval_squeeze(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("squeeze", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Tensor(t.squeeze()))
}

pub fn eval_unsqueeze(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("unsqueeze requires tensor and dim".into()));
    }
    let t = get_tensor(&args[0])?;
    let dim = args[1].as_f64()? as usize;
    Ok(MathValue::Tensor(t.unsqueeze(dim)?))
}

// ==========================================================================
// Tensor Properties
// ==========================================================================

pub fn eval_shape(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("shape", args, 1)?;
    let t = get_tensor(&args[0])?;
    let shape_data: Vec<f64> = t.shape.iter().map(|&s| s as f64).collect();
    Ok(MathValue::Tensor(Tensor::new(
        shape_data.clone(),
        vec![shape_data.len()],
    )?))
}

pub fn eval_ndim(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("ndim", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Int(t.ndim() as i64))
}

pub fn eval_numel(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("numel", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Int(t.numel() as i64))
}

pub fn eval_item(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("item", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Float(t.item()?))
}

// ==========================================================================
// Tensor Reductions
// ==========================================================================

pub fn eval_sum_tensor(args: &[MathValue]) -> Result<MathValue, CompileError> {
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Float(t.sum()))
}

pub fn eval_mean(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() == 1 && args[0].is_tensor() {
        let t = get_tensor(&args[0])?;
        Ok(MathValue::Float(t.mean()))
    } else {
        // Mean of arguments
        let vals: Vec<f64> = args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
        if vals.is_empty() {
            return Err(CompileError::Semantic("mean requires at least 1 argument".into()));
        }
        Ok(MathValue::Float(vals.iter().sum::<f64>() / vals.len() as f64))
    }
}

pub fn eval_var(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("var", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Float(t.var()))
}

pub fn eval_std(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("std", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Float(t.std()))
}

pub fn eval_argmin(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("argmin", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Int(t.argmin() as i64))
}

pub fn eval_argmax(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("argmax", args, 1)?;
    let t = get_tensor(&args[0])?;
    Ok(MathValue::Int(t.argmax() as i64))
}

// ==========================================================================
// Activation Functions (ML-oriented)
// ==========================================================================

pub fn eval_relu(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("relu requires 1 argument".into()));
    }
    match &args[0] {
        MathValue::Tensor(t) => Ok(MathValue::Tensor(t.relu())),
        v => {
            let x = v.as_f64()?;
            Ok(MathValue::Float(x.max(0.0)))
        }
    }
}

pub fn eval_sigmoid(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("sigmoid requires 1 argument".into()));
    }
    match &args[0] {
        MathValue::Tensor(t) => Ok(MathValue::Tensor(t.sigmoid())),
        v => {
            let x = v.as_f64()?;
            Ok(MathValue::Float(1.0 / (1.0 + (-x).exp())))
        }
    }
}

pub fn eval_softmax(args: &[MathValue]) -> Result<MathValue, CompileError> {
    require_tensor_args("softmax", args, 1)?;
    let t = get_tensor(&args[0])?;
    // Compute softmax (for 1D or last dim)
    let max_val = t.max();
    let exp_data: Vec<f64> = t.data.iter().map(|&x| (x - max_val).exp()).collect();
    let sum: f64 = exp_data.iter().sum();
    let softmax_data: Vec<f64> = exp_data.iter().map(|&x| x / sum).collect();
    Ok(MathValue::Tensor(Tensor::new(softmax_data, t.shape.clone())?))
}

pub fn eval_tanh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("tanh requires 1 argument".into()));
    }
    match &args[0] {
        MathValue::Tensor(t) => Ok(MathValue::Tensor(t.tanh())),
        v => {
            let x = v.as_f64()?;
            Ok(MathValue::Float(x.tanh()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zeros() {
        let result = eval_zeros(&[MathValue::Int(3)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.shape, vec![3]);
                assert!(t.data.iter().all(|&x| x == 0.0));
            }
            _ => panic!("expected tensor"),
        }
    }

    #[test]
    fn test_ones() {
        let result = eval_ones(&[MathValue::Int(2), MathValue::Int(2)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.shape, vec![2, 2]);
                assert!(t.data.iter().all(|&x| x == 1.0));
            }
            _ => panic!("expected tensor"),
        }
    }

    #[test]
    fn test_eye() {
        let result = eval_eye(&[MathValue::Int(3)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.shape, vec![3, 3]);
                assert_eq!(t.data[0], 1.0); // (0,0)
                assert_eq!(t.data[4], 1.0); // (1,1)
                assert_eq!(t.data[8], 1.0); // (2,2)
            }
            _ => panic!("expected tensor"),
        }
    }

    #[test]
    fn test_arange() {
        let result = eval_arange(&[MathValue::Int(5)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.shape, vec![5]);
                assert_eq!(t.data, vec![0.0, 1.0, 2.0, 3.0, 4.0]);
            }
            _ => panic!("expected tensor"),
        }
    }

    #[test]
    fn test_relu() {
        let t = Tensor::new(vec![-1.0, 0.0, 1.0, 2.0], vec![4]).unwrap();
        let result = eval_relu(&[MathValue::Tensor(t)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.data, vec![0.0, 0.0, 1.0, 2.0]);
            }
            _ => panic!("expected tensor"),
        }
    }

    #[test]
    fn test_mean_scalars() {
        let result = eval_mean(&[MathValue::Int(1), MathValue::Int(2), MathValue::Int(3)]).unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 2.0).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_shape() {
        let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        let result = eval_shape(&[MathValue::Tensor(t)]).unwrap();
        match result {
            MathValue::Tensor(t) => {
                assert_eq!(t.data, vec![2.0, 2.0]);
            }
            _ => panic!("expected tensor"),
        }
    }
}

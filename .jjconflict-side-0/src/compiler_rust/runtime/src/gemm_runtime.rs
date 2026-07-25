const MATRIX_F64_MAGIC: u64 = 0x5349_4D50_4C45_4D58;

#[repr(C)]
pub struct SimpleRuntimeMatrixF64 {
    magic: u64,
    rows: i64,
    cols: i64,
    len: i64,
    data: *mut f64,
}

fn checked_len(rows: i64, cols: i64) -> Option<usize> {
    if rows <= 0 || cols <= 0 {
        return None;
    }
    rows.checked_mul(cols).map(|v| v as usize)
}

unsafe fn matrix_from_handle(handle: i64) -> Option<&'static SimpleRuntimeMatrixF64> {
    if handle == 0 {
        return None;
    }
    let matrix = &*(handle as *const SimpleRuntimeMatrixF64);
    if matrix.magic != MATRIX_F64_MAGIC {
        return None;
    }
    let len = checked_len(matrix.rows, matrix.cols)?;
    if matrix.len != len as i64 || matrix.data.is_null() {
        return None;
    }
    Some(matrix)
}

fn allocate_matrix(rows: i64, cols: i64, mut values: Vec<f64>) -> i64 {
    let Some(len) = checked_len(rows, cols) else {
        return 0;
    };
    if values.len() != len {
        return 0;
    }
    let data = values.as_mut_ptr();
    std::mem::forget(values);
    Box::into_raw(Box::new(SimpleRuntimeMatrixF64 {
        magic: MATRIX_F64_MAGIC,
        rows,
        cols,
        len: len as i64,
        data,
    })) as i64
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_matrix_f64_new(data: *const f64, rows: i64, cols: i64) -> i64 {
    let Some(len) = checked_len(rows, cols) else {
        return 0;
    };
    if data.is_null() {
        return 0;
    }
    let values = std::slice::from_raw_parts(data, len).to_vec();
    allocate_matrix(rows, cols, values)
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_matrix_f64_free(handle: i64) {
    let Some(matrix) = matrix_from_handle(handle) else {
        return;
    };
    let ptr = handle as *mut SimpleRuntimeMatrixF64;
    let data = Vec::from_raw_parts(matrix.data, matrix.len as usize, matrix.len as usize);
    drop(data);
    drop(Box::from_raw(ptr));
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_matrix_f64_rows(handle: i64) -> i64 {
    matrix_from_handle(handle).map(|m| m.rows).unwrap_or(0)
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_matrix_f64_cols(handle: i64) -> i64 {
    matrix_from_handle(handle).map(|m| m.cols).unwrap_or(0)
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_matrix_f64_get(handle: i64, row: i64, col: i64) -> f64 {
    let Some(matrix) = matrix_from_handle(handle) else {
        return f64::NAN;
    };
    if row < 0 || col < 0 || row >= matrix.rows || col >= matrix.cols {
        return f64::NAN;
    }
    *matrix.data.add((row * matrix.cols + col) as usize)
}

#[no_mangle]
pub unsafe extern "C" fn __simple_runtime_gemm_add(a: i64, b: i64, c: i64) -> i64 {
    let Some(a_matrix) = matrix_from_handle(a) else {
        return 0;
    };
    let Some(b_matrix) = matrix_from_handle(b) else {
        return 0;
    };
    let Some(c_matrix) = matrix_from_handle(c) else {
        return 0;
    };
    if a_matrix.cols != b_matrix.rows || c_matrix.rows != a_matrix.rows || c_matrix.cols != b_matrix.cols {
        return 0;
    }

    let rows = a_matrix.rows;
    let cols = b_matrix.cols;
    let inner = a_matrix.cols;
    let mut out = vec![0.0; (rows * cols) as usize];
    for row in 0..rows {
        for col in 0..cols {
            let mut total = *c_matrix.data.add((row * cols + col) as usize);
            for k in 0..inner {
                let a_value = *a_matrix.data.add((row * inner + k) as usize);
                let b_value = *b_matrix.data.add((k * cols + col) as usize);
                total += a_value * b_value;
            }
            out[(row * cols + col) as usize] = total;
        }
    }
    allocate_matrix(rows, cols, out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gemm_add_computes_rectangular_row_major_result() {
        let a = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
        let b = [7.0, 8.0, 9.0, 10.0, 11.0, 12.0];
        let c = [1.0, 2.0, 3.0, 4.0];
        unsafe {
            let ah = __simple_runtime_matrix_f64_new(a.as_ptr(), 2, 3);
            let bh = __simple_runtime_matrix_f64_new(b.as_ptr(), 3, 2);
            let ch = __simple_runtime_matrix_f64_new(c.as_ptr(), 2, 2);
            let out = __simple_runtime_gemm_add(ah, bh, ch);
            assert_ne!(out, 0);
            assert_eq!(__simple_runtime_matrix_f64_rows(out), 2);
            assert_eq!(__simple_runtime_matrix_f64_cols(out), 2);
            assert_eq!(__simple_runtime_matrix_f64_get(out, 0, 0), 59.0);
            assert_eq!(__simple_runtime_matrix_f64_get(out, 0, 1), 66.0);
            assert_eq!(__simple_runtime_matrix_f64_get(out, 1, 0), 142.0);
            assert_eq!(__simple_runtime_matrix_f64_get(out, 1, 1), 158.0);
            __simple_runtime_matrix_f64_free(ah);
            __simple_runtime_matrix_f64_free(bh);
            __simple_runtime_matrix_f64_free(ch);
            __simple_runtime_matrix_f64_free(out);
        }
    }

    #[test]
    fn gemm_add_rejects_shape_mismatch() {
        let a = [1.0, 2.0, 3.0, 4.0];
        let b = [1.0, 2.0, 3.0, 4.0];
        let c = [0.0, 0.0, 0.0];
        unsafe {
            let ah = __simple_runtime_matrix_f64_new(a.as_ptr(), 2, 2);
            let bh = __simple_runtime_matrix_f64_new(b.as_ptr(), 2, 2);
            let ch = __simple_runtime_matrix_f64_new(c.as_ptr(), 3, 1);
            assert_eq!(__simple_runtime_gemm_add(ah, bh, ch), 0);
            __simple_runtime_matrix_f64_free(ah);
            __simple_runtime_matrix_f64_free(bh);
            __simple_runtime_matrix_f64_free(ch);
        }
    }
}

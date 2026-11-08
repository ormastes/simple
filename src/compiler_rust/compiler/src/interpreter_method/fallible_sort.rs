use std::cmp::Ordering;

/// Stable merge sort that stops at the first comparator error. The caller
/// publishes the returned vector only on success, preserving its receiver on
/// an error without disguising it as an arbitrary comparator ordering.
pub(super) fn stable_sort_by<T: Clone, E>(
    values: &[T],
    compare: &mut impl FnMut(&T, &T) -> Result<Ordering, E>,
) -> Result<Vec<T>, E> {
    if values.len() < 2 {
        return Ok(values.to_vec());
    }
    let middle = values.len() / 2;
    let left = stable_sort_by(&values[..middle], compare)?;
    let right = stable_sort_by(&values[middle..], compare)?;
    let mut result = Vec::with_capacity(values.len());
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        if compare(&left[i], &right[j])? != Ordering::Greater {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_equal_key_order_and_input() {
        let input = [(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd')];
        let sorted = stable_sort_by(&input, &mut |a, b| Ok::<_, ()>(a.0.cmp(&b.0))).unwrap();
        assert_eq!(sorted, [(1, 'b'), (1, 'd'), (2, 'a'), (2, 'c')]);
        assert_eq!(input, [(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd')]);
    }

    #[test]
    fn stops_at_first_error() {
        let mut calls = 0;
        let result = stable_sort_by(&[4, 3, 2, 1], &mut |_, _| {
            calls += 1;
            Err::<Ordering, _>("comparator failed")
        });
        assert_eq!(result, Err("comparator failed"));
        assert_eq!(calls, 1);
    }

    #[test]
    fn empty_and_singleton_do_not_call_comparator() {
        for input in [vec![], vec![7]] {
            let output = stable_sort_by(&input, &mut |_, _| -> Result<Ordering, ()> {
                panic!("no comparison needed")
            }).unwrap();
            assert_eq!(output, input);
        }
    }
}

// F32 SIMD implementations
// This file is included by types.rs

// =============================================================================
// F32x4 Implementation
// =============================================================================

impl F32x4 {
    pub const LANES: usize = 4;

    /// Create a new vector from an array.
    #[inline]
    pub fn new(values: [f32; 4]) -> Self {
        F32x4(values)
    }

    /// Create a vector with all lanes set to the same value.
    #[inline]
    pub fn splat(value: f32) -> Self {
        F32x4([value; 4])
    }

    /// Create a zero vector.
    #[inline]
    pub fn zero() -> Self {
        F32x4([0.0; 4])
    }

    /// Extract a single lane.
    #[inline]
    pub fn extract(&self, index: usize) -> f32 {
        self.0[index]
    }

    /// Create a new vector with one lane replaced.
    #[inline]
    pub fn with(&self, index: usize, value: f32) -> Self {
        let mut result = *self;
        result.0[index] = value;
        result
    }

    /// Load from a slice (must have at least 4 elements from offset).
    #[inline]
    pub fn load(slice: &[f32], offset: usize) -> Self {
        F32x4([
            slice[offset],
            slice[offset + 1],
            slice[offset + 2],
            slice[offset + 3],
        ])
    }

    /// Store to a slice.
    #[inline]
    pub fn store(&self, slice: &mut [f32], offset: usize) {
        slice[offset] = self.0[0];
        slice[offset + 1] = self.0[1];
        slice[offset + 2] = self.0[2];
        slice[offset + 3] = self.0[3];
    }

    /// Horizontal sum of all lanes.
    #[inline]
    pub fn sum(&self) -> f32 {
        self.0[0] + self.0[1] + self.0[2] + self.0[3]
    }

    /// Horizontal product of all lanes.
    #[inline]
    pub fn product(&self) -> f32 {
        self.0[0] * self.0[1] * self.0[2] * self.0[3]
    }

    /// Minimum value across all lanes.
    #[inline]
    pub fn min_element(&self) -> f32 {
        self.0.iter().cloned().fold(f32::INFINITY, f32::min)
    }

    /// Maximum value across all lanes.
    #[inline]
    pub fn max_element(&self) -> f32 {
        self.0.iter().cloned().fold(f32::NEG_INFINITY, f32::max)
    }

    /// Lane-wise minimum.
    #[inline]
    pub fn min(&self, other: Self) -> Self {
        F32x4([
            self.0[0].min(other.0[0]),
            self.0[1].min(other.0[1]),
            self.0[2].min(other.0[2]),
            self.0[3].min(other.0[3]),
        ])
    }

    /// Lane-wise maximum.
    #[inline]
    pub fn max(&self, other: Self) -> Self {
        F32x4([
            self.0[0].max(other.0[0]),
            self.0[1].max(other.0[1]),
            self.0[2].max(other.0[2]),
            self.0[3].max(other.0[3]),
        ])
    }

    /// Lane-wise absolute value.
    #[inline]
    pub fn abs(&self) -> Self {
        F32x4([
            self.0[0].abs(),
            self.0[1].abs(),
            self.0[2].abs(),
            self.0[3].abs(),
        ])
    }

    /// Lane-wise square root.
    #[inline]
    pub fn sqrt(&self) -> Self {
        F32x4([
            self.0[0].sqrt(),
            self.0[1].sqrt(),
            self.0[2].sqrt(),
            self.0[3].sqrt(),
        ])
    }

    /// Lane-wise reciprocal (1/x).
    #[inline]
    pub fn recip(&self) -> Self {
        F32x4([
            1.0 / self.0[0],
            1.0 / self.0[1],
            1.0 / self.0[2],
            1.0 / self.0[3],
        ])
    }

    /// Lane-wise floor.
    #[inline]
    pub fn floor(&self) -> Self {
        F32x4([
            self.0[0].floor(),
            self.0[1].floor(),
            self.0[2].floor(),
            self.0[3].floor(),
        ])
    }

    /// Lane-wise ceil.
    #[inline]
    pub fn ceil(&self) -> Self {
        F32x4([
            self.0[0].ceil(),
            self.0[1].ceil(),
            self.0[2].ceil(),
            self.0[3].ceil(),
        ])
    }

    /// Lane-wise round.
    #[inline]
    pub fn round(&self) -> Self {
        F32x4([
            self.0[0].round(),
            self.0[1].round(),
            self.0[2].round(),
            self.0[3].round(),
        ])
    }

    /// Fused multiply-add: self * a + b.
    #[inline]
    pub fn fma(&self, a: Self, b: Self) -> Self {
        F32x4([
            self.0[0].mul_add(a.0[0], b.0[0]),
            self.0[1].mul_add(a.0[1], b.0[1]),
            self.0[2].mul_add(a.0[2], b.0[2]),
            self.0[3].mul_add(a.0[3], b.0[3]),
        ])
    }

    /// Compare less-than, returning a mask.
    #[inline]
    pub fn lt(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] < other.0[0] { -1 } else { 0 },
            if self.0[1] < other.0[1] { -1 } else { 0 },
            if self.0[2] < other.0[2] { -1 } else { 0 },
            if self.0[3] < other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare less-than-or-equal, returning a mask.
    #[inline]
    pub fn le(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] <= other.0[0] { -1 } else { 0 },
            if self.0[1] <= other.0[1] { -1 } else { 0 },
            if self.0[2] <= other.0[2] { -1 } else { 0 },
            if self.0[3] <= other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare greater-than, returning a mask.
    #[inline]
    pub fn gt(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] > other.0[0] { -1 } else { 0 },
            if self.0[1] > other.0[1] { -1 } else { 0 },
            if self.0[2] > other.0[2] { -1 } else { 0 },
            if self.0[3] > other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare equal, returning a mask.
    #[inline]
    pub fn eq(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] == other.0[0] { -1 } else { 0 },
            if self.0[1] == other.0[1] { -1 } else { 0 },
            if self.0[2] == other.0[2] { -1 } else { 0 },
            if self.0[3] == other.0[3] { -1 } else { 0 },
        ])
    }

    /// Select lanes based on mask: mask ? self : other.
    #[inline]
    pub fn select(mask: Mask32x4, if_true: Self, if_false: Self) -> Self {
        F32x4([
            if mask.0[0] != 0 { if_true.0[0] } else { if_false.0[0] },
            if mask.0[1] != 0 { if_true.0[1] } else { if_false.0[1] },
            if mask.0[2] != 0 { if_true.0[2] } else { if_false.0[2] },
            if mask.0[3] != 0 { if_true.0[3] } else { if_false.0[3] },
        ])
    }

    /// Shuffle lanes based on indices.
    #[inline]
    pub fn shuffle(&self, indices: [usize; 4]) -> Self {
        F32x4([
            self.0[indices[0]],
            self.0[indices[1]],
            self.0[indices[2]],
            self.0[indices[3]],
        ])
    }

    /// Swizzle: get lanes by name (0=x, 1=y, 2=z, 3=w).
    #[inline]
    pub fn x(&self) -> f32 { self.0[0] }
    #[inline]
    pub fn y(&self) -> f32 { self.0[1] }
    #[inline]
    pub fn z(&self) -> f32 { self.0[2] }
    #[inline]
    pub fn w(&self) -> f32 { self.0[3] }

    /// Gather from slice using indices.
    #[inline]
    pub fn gather(slice: &[f32], indices: I32x4) -> Self {
        F32x4([
            slice[indices.0[0] as usize],
            slice[indices.0[1] as usize],
            slice[indices.0[2] as usize],
            slice[indices.0[3] as usize],
        ])
    }

    /// Scatter to slice using indices.
    #[inline]
    pub fn scatter(&self, slice: &mut [f32], indices: I32x4) {
        slice[indices.0[0] as usize] = self.0[0];
        slice[indices.0[1] as usize] = self.0[1];
        slice[indices.0[2] as usize] = self.0[2];
        slice[indices.0[3] as usize] = self.0[3];
    }
}

impl fmt::Debug for F32x4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "F32x4({:?})", self.0)
    }
}

impl Default for F32x4 {
    fn default() -> Self {
        Self::zero()
    }
}

impl Index<usize> for F32x4 {
    type Output = f32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl Add for F32x4 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }
}

impl Sub for F32x4 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }
}

impl Mul for F32x4 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] * rhs.0[0],
            self.0[1] * rhs.0[1],
            self.0[2] * rhs.0[2],
            self.0[3] * rhs.0[3],
        ])
    }
}

impl Div for F32x4 {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] / rhs.0[0],
            self.0[1] / rhs.0[1],
            self.0[2] / rhs.0[2],
            self.0[3] / rhs.0[3],
        ])
    }
}

impl Neg for F32x4 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        F32x4([-self.0[0], -self.0[1], -self.0[2], -self.0[3]])
    }
}

// Scalar operations
impl Add<f32> for F32x4 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: f32) -> Self::Output {
        self + F32x4::splat(rhs)
    }
}

impl Mul<f32> for F32x4 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: f32) -> Self::Output {
        self * F32x4::splat(rhs)
    }
}


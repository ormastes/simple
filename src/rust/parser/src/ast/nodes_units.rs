// Unit type definitions for ast/nodes module

#[derive(Debug, Clone, PartialEq)]
pub struct UnitDef {
    pub span: Span,
    pub name: String,          // e.g., "UserId" or "IpAddr"
    pub base_types: Vec<Type>, // e.g., [i64] or [str, u32] for multi-base units
    pub suffix: String,        // e.g., "uid" or "ip" (for literals like 42_uid or "127.0.0.1"_ip)
    pub visibility: Visibility,
}

/// Handle pool declaration for a type
/// ```simple
/// handle_pool Enemy:
///     capacity: 1024
/// ```
/// Declares a global handle pool for allocating handles to a specific type.
/// Required before using `new+ T(...)` syntax.
#[derive(Debug, Clone, PartialEq)]
pub struct HandlePoolDef {
    pub span: Span,
    pub type_name: String,         // The type this pool manages (e.g., "Enemy")
    pub capacity: Option<u64>,      // Optional initial capacity
    pub visibility: Visibility,
}

/// Unit variant in a unit family
/// e.g., `m = 1.0` or `km = 1000.0`
#[derive(Debug, Clone, PartialEq)]
pub struct UnitVariant {
    pub suffix: String, // e.g., "m", "km"
    pub factor: f64,    // conversion factor to base unit
}

/// Unit family definition: `unit length(base: f64): m = 1.0, km = 1000.0`
/// Defines a family of related units with conversion factors
#[derive(Debug, Clone, PartialEq)]
pub struct UnitFamilyDef {
    pub span: Span,
    pub name: String,    // e.g., "length"
    pub base_type: Type, // e.g., f64
    pub variants: Vec<UnitVariant>,
    pub visibility: Visibility,
    /// Optional arithmetic rules block
    pub arithmetic: Option<UnitArithmetic>,
}

/// Arithmetic rules for a unit family
/// Defines allowed operations like `allow add(length) -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct UnitArithmetic {
    pub binary_rules: Vec<BinaryArithmeticRule>,
    pub unary_rules: Vec<UnaryArithmeticRule>,
    pub custom_fns: Vec<FunctionDef>,
    /// Allowed representations: repr: u8, u12, i16, f32, ...
    pub allowed_reprs: Vec<ReprType>,
}

/// Representation type for bit-limited units
/// Examples: u8, u12, i16, i24, f32, f64
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReprType {
    pub signed: bool,      // true for i/f, false for u
    pub bits: u8,          // bit width (8, 12, 16, 24, 32, 64)
    pub is_float: bool,    // true for f16, f32, f64
}

impl ReprType {
    pub fn new(signed: bool, bits: u8, is_float: bool) -> Self {
        Self { signed, bits, is_float }
    }

    /// Parse from string like "u8", "i12", "f32"
    pub fn from_str(s: &str) -> Option<Self> {
        if s.is_empty() {
            return None;
        }
        let (prefix, rest) = s.split_at(1);
        let bits: u8 = rest.parse().ok()?;
        match prefix {
            "u" => Some(Self::new(false, bits, false)),
            "i" => Some(Self::new(true, bits, false)),
            "f" => Some(Self::new(true, bits, true)),
            _ => None,
        }
    }

    /// Convert to string like "u8", "i12", "f32"
    pub fn to_string(&self) -> String {
        let prefix = if self.is_float {
            "f"
        } else if self.signed {
            "i"
        } else {
            "u"
        };
        format!("{}{}", prefix, self.bits)
    }
}

/// Overflow behavior for bit-limited units
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OverflowBehavior {
    /// Default: panic in debug, undefined in release
    #[default]
    Default,
    /// Always panic on overflow
    Checked,
    /// Clamp to min/max
    Saturate,
    /// Modular arithmetic (wrap around)
    Wrap,
}

/// Constraints for unit type with representation
/// Used in `where` clause: `_cm:u8 where checked` or `_cm where range: 0..100`
#[derive(Debug, Clone, PartialEq, Default)]
pub struct UnitReprConstraints {
    /// Explicit representation type (from compact syntax `_cm:u12`)
    pub repr: Option<ReprType>,
    /// Range constraint for auto-inferring bit width
    pub range: Option<(i64, i64)>,
    /// Overflow behavior
    pub overflow: OverflowBehavior,
    /// Default value expression
    pub default_value: Option<Box<Expr>>,
}

/// Binary arithmetic operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryArithmeticOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

/// Unary arithmetic operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryArithmeticOp {
    Neg,
    Abs,
}

/// Binary arithmetic rule: `allow add(length) -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryArithmeticRule {
    pub op: BinaryArithmeticOp,
    pub operand_type: Type,
    pub result_type: Type,
}

/// Unary arithmetic rule: `allow neg -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryArithmeticRule {
    pub op: UnaryArithmeticOp,
    pub result_type: Type,
}

/// Compound unit definition: `unit velocity = length / time`
/// Defines derived units from base unit families
#[derive(Debug, Clone, PartialEq)]
pub struct CompoundUnitDef {
    pub span: Span,
    pub name: String,         // e.g., "velocity"
    pub expr: UnitExpr,       // e.g., length / time
    pub arithmetic: Option<UnitArithmetic>,
    pub visibility: Visibility,
}

/// Unit expression for compound units
#[derive(Debug, Clone, PartialEq)]
pub enum UnitExpr {
    /// Base unit family reference
    Base(String),
    /// Multiplication: length * length
    Mul(Box<UnitExpr>, Box<UnitExpr>),
    /// Division: length / time
    Div(Box<UnitExpr>, Box<UnitExpr>),
    /// Power: time^2
    Pow(Box<UnitExpr>, i32),
}

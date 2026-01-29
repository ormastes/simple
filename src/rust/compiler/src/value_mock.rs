// Mock and Spy types for testing
//
// This module provides mock objects for unit testing, supporting:
// - Method stubbing with configurable return values
// - Call recording and verification
// - Argument matching

/// Configuration for a mocked method
#[derive(Debug, Clone)]
pub struct MockMethodConfig {
    /// Return value when called (None means return Nil)
    pub return_value: Option<super::Value>,
    /// Queue of return values for sequential calls
    pub return_queue: Vec<super::Value>,
    /// Argument matchers for conditional returns
    pub arg_matchers: Vec<(Vec<MatcherValue>, super::Value)>,
}

impl Default for MockMethodConfig {
    fn default() -> Self {
        Self {
            return_value: None,
            return_queue: Vec::new(),
            arg_matchers: Vec::new(),
        }
    }
}

/// Record of a method call
#[derive(Debug, Clone)]
pub struct MockCallRecord {
    /// Method name that was called
    pub method: String,
    /// Arguments passed to the method
    pub args: Vec<super::Value>,
}

/// Mock object for testing
#[derive(Debug, Clone)]
pub struct MockValue {
    /// Type name being mocked
    pub type_name: String,
    /// Method configurations (stubbing)
    pub methods: Arc<Mutex<HashMap<String, MockMethodConfig>>>,
    /// Record of all calls made
    pub calls: Arc<Mutex<Vec<MockCallRecord>>>,
    /// Whether this is a spy (calls through to real implementation)
    pub is_spy: bool,
    /// Current method being configured (for chained .when().returns() calls)
    pub configuring_method: Arc<Mutex<Option<String>>>,
    /// Current argument matchers being configured
    pub configuring_args: Arc<Mutex<Vec<MatcherValue>>>,
}

impl MockValue {
    /// Create a new mock for the given type
    pub fn new(type_name: String) -> Self {
        Self {
            type_name,
            methods: Arc::new(Mutex::new(HashMap::new())),
            calls: Arc::new(Mutex::new(Vec::new())),
            is_spy: false,
            configuring_method: Arc::new(Mutex::new(None)),
            configuring_args: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Create a new spy for the given type
    pub fn new_spy(type_name: String) -> Self {
        Self {
            type_name,
            methods: Arc::new(Mutex::new(HashMap::new())),
            calls: Arc::new(Mutex::new(Vec::new())),
            is_spy: true,
            configuring_method: Arc::new(Mutex::new(None)),
            configuring_args: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Configure a method for stubbing
    pub fn when_method(&self, method: &str) {
        let mut configuring = self.configuring_method.lock().unwrap();
        *configuring = Some(method.to_string());
        // Clear any previous arg matchers
        let mut args = self.configuring_args.lock().unwrap();
        args.clear();
    }

    /// Set argument matchers for the current method configuration
    pub fn with_args(&self, matchers: Vec<MatcherValue>) {
        let mut args = self.configuring_args.lock().unwrap();
        *args = matchers;
    }

    /// Set return value for the currently configured method
    pub fn returns(&self, value: super::Value) {
        let configuring = self.configuring_method.lock().unwrap();
        if let Some(ref method) = *configuring {
            let mut methods = self.methods.lock().unwrap();
            let config = methods.entry(method.clone()).or_default();
            
            let args = self.configuring_args.lock().unwrap();
            if args.is_empty() {
                config.return_value = Some(value);
            } else {
                config.arg_matchers.push((args.clone(), value));
            }
        }
    }

    /// Set return value for next call only
    pub fn returns_once(&self, value: super::Value) {
        let configuring = self.configuring_method.lock().unwrap();
        if let Some(ref method) = *configuring {
            let mut methods = self.methods.lock().unwrap();
            let config = methods.entry(method.clone()).or_default();
            config.return_queue.push(value);
        }
    }

    /// Record a method call
    pub fn record_call(&self, method: &str, args: Vec<super::Value>) {
        let mut calls = self.calls.lock().unwrap();
        calls.push(MockCallRecord {
            method: method.to_string(),
            args,
        });
    }

    /// Get return value for a method call
    pub fn get_return_value(&self, method: &str, args: &[super::Value]) -> super::Value {
        let mut methods = self.methods.lock().unwrap();
        if let Some(config) = methods.get_mut(method) {
            // Check return queue first (for returnsOnce)
            if !config.return_queue.is_empty() {
                return config.return_queue.remove(0);
            }
            
            // Check argument matchers
            for (matchers, return_val) in &config.arg_matchers {
                if matchers_match(matchers, args) {
                    return return_val.clone();
                }
            }
            
            // Return default value
            if let Some(ref val) = config.return_value {
                return val.clone();
            }
        }
        super::Value::Nil
    }

    /// Check if a method was called
    pub fn was_called(&self, method: &str) -> bool {
        let calls = self.calls.lock().unwrap();
        calls.iter().any(|c| c.method == method)
    }

    /// Count how many times a method was called
    pub fn call_count(&self, method: &str) -> usize {
        let calls = self.calls.lock().unwrap();
        calls.iter().filter(|c| c.method == method).count()
    }

    /// Check if a method was called with specific arguments
    pub fn was_called_with(&self, method: &str, expected_args: &[super::Value]) -> bool {
        let calls = self.calls.lock().unwrap();
        calls.iter().any(|c| {
            c.method == method && args_match(&c.args, expected_args)
        })
    }

    /// Get all calls to a method
    pub fn get_calls(&self, method: &str) -> Vec<Vec<super::Value>> {
        let calls = self.calls.lock().unwrap();
        calls.iter()
            .filter(|c| c.method == method)
            .map(|c| c.args.clone())
            .collect()
    }

    /// Reset all call records
    pub fn reset(&self) {
        let mut calls = self.calls.lock().unwrap();
        calls.clear();
    }
}

/// Argument matcher for flexible mock verification
#[derive(Debug, Clone)]
pub enum MatcherValue {
    /// Match any value
    Any,
    /// Match exact value
    Exact(Box<super::Value>),
    /// Match value greater than
    GreaterThan(i64),
    /// Match value less than
    LessThan(i64),
    /// Match value greater than or equal
    GreaterOrEqual(i64),
    /// Match value less than or equal
    LessOrEqual(i64),
    /// Match string containing substring
    Contains(String),
    /// Match string starting with prefix
    StartsWith(String),
    /// Match string ending with suffix
    EndsWith(String),
    /// Match value of specific type
    OfType(String),
    /// Match using custom predicate (stored as lambda)
    Custom(Box<super::Value>),
    /// BDD matcher: expect value to be true
    BeTrue,
    /// BDD matcher: expect value to be false
    BeFalse,
}

impl MatcherValue {
    /// Check if a value matches this matcher
    pub fn matches(&self, value: &super::Value) -> bool {
        match self {
            MatcherValue::Any => true,
            MatcherValue::Exact(expected) => values_equal(value, expected),
            MatcherValue::GreaterThan(n) => match value {
                super::Value::Int(v) => *v > *n,
                super::Value::Float(v) => *v > (*n as f64),
                _ => false,
            },
            MatcherValue::LessThan(n) => match value {
                super::Value::Int(v) => *v < *n,
                super::Value::Float(v) => *v < (*n as f64),
                _ => false,
            },
            MatcherValue::GreaterOrEqual(n) => match value {
                super::Value::Int(v) => *v >= *n,
                super::Value::Float(v) => *v >= (*n as f64),
                _ => false,
            },
            MatcherValue::LessOrEqual(n) => match value {
                super::Value::Int(v) => *v <= *n,
                super::Value::Float(v) => *v <= (*n as f64),
                _ => false,
            }
            MatcherValue::Contains(s) => {
                if let super::Value::Str(v) = value {
                    v.contains(s)
                } else {
                    false
                }
            }
            MatcherValue::StartsWith(s) => {
                if let super::Value::Str(v) = value {
                    v.starts_with(s)
                } else {
                    false
                }
            }
            MatcherValue::EndsWith(s) => {
                if let super::Value::Str(v) = value {
                    v.ends_with(s)
                } else {
                    false
                }
            }
            MatcherValue::OfType(type_name) => {
                let actual_type = match value {
                    super::Value::Int(_) => "Int",
                    super::Value::Float(_) => "Float",
                    super::Value::Bool(_) => "Bool",
                    super::Value::Str(_) => "String",
                    super::Value::Array(_) => "Array",
                    super::Value::Dict(_) => "Dict",
                    super::Value::Object { class, .. } => class.as_str(),
                    _ => "Unknown",
                };
                actual_type == type_name
            }
            MatcherValue::Custom(_) => {
                // Custom matchers would need interpreter access to evaluate
                // For now, just return true
                true
            }
            MatcherValue::BeTrue => matches!(value, super::Value::Bool(true)),
            MatcherValue::BeFalse => matches!(value, super::Value::Bool(false)),
        }
    }
}

/// Check if matchers match arguments
fn matchers_match(matchers: &[MatcherValue], args: &[super::Value]) -> bool {
    if matchers.len() != args.len() {
        return false;
    }
    matchers.iter().zip(args.iter()).all(|(m, a)| m.matches(a))
}

/// Check if two argument lists match (for verification)
fn args_match(actual: &[super::Value], expected: &[super::Value]) -> bool {
    if actual.len() != expected.len() {
        return false;
    }
    actual.iter().zip(expected.iter()).all(|(a, e)| values_equal(a, e))
}

/// Check if two values are equal
fn values_equal(a: &super::Value, b: &super::Value) -> bool {
    match (a, b) {
        (super::Value::Int(x), super::Value::Int(y)) => x == y,
        (super::Value::Float(x), super::Value::Float(y)) => (x - y).abs() < f64::EPSILON,
        (super::Value::Bool(x), super::Value::Bool(y)) => x == y,
        (super::Value::Str(x), super::Value::Str(y)) => x == y,
        (super::Value::Symbol(x), super::Value::Symbol(y)) => x == y,
        (super::Value::Nil, super::Value::Nil) => true,
        (super::Value::Array(x), super::Value::Array(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| values_equal(a, b))
        }
        _ => false,
    }
}

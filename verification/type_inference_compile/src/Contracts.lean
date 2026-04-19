-- Contracts.lean - Formal model for contract verification


inductive Val
  | i32 : Int → Val
  | bool : Bool → Val
  | str : String → Val
  | nil
  | error : String → Val → Val

inductive ContractExpr
  | val : Val → ContractExpr
  | var : String → ContractExpr
  | old : ContractExpr → ContractExpr
  | ret
  | err
  | binOp : String → ContractExpr → ContractExpr → ContractExpr
  | unOp : String → ContractExpr → ContractExpr

structure ContractClause where
  condition : ContractExpr
  message : Option String

structure FunctionContract where
  preconditions : List ContractClause
  invariants : List ContractClause
  postconditions : List ContractClause
  errorPostconditions : List ContractClause

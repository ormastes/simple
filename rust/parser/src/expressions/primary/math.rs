use crate::ast::{Expr, TensorMode, TensorSlice};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_math(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Grid => self.parse_grid_literal(),
            TokenKind::Tensor => self.parse_tensor_literal(),
            _ => Err(ParseError::unexpected_token(
                "math literal",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // ========================================================================
    // Simple Math: Grid/Tensor Literal Parsing (#1910-#1919)
    // ========================================================================

    /// Parse grid literal: grid device="cuda": | row | row |
    fn parse_grid_literal(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'grid'

        // Optional device parameter: grid device="cuda":
        let device = if self.check_ident("device") {
            self.advance(); // consume 'device'
            self.expect(&TokenKind::Assign)?;
            match &self.current.kind {
                TokenKind::String(s) => {
                    let dev = s.clone();
                    self.advance();
                    Some(dev)
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "string literal for device",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let rows = self.parse_grid_rows()?;

        self.expect(&TokenKind::Dedent)?;

        // Box all expressions in rows
        let boxed_rows = rows
            .into_iter()
            .map(|row| row.into_iter().map(Box::new).collect())
            .collect();

        Ok(Expr::GridLiteral {
            rows: boxed_rows,
            device,
        })
    }

    /// Parse grid rows: | cell | cell | ...
    fn parse_grid_rows(&mut self) -> Result<Vec<Vec<Expr>>, ParseError> {
        let mut rows = Vec::new();

        while self.check(&TokenKind::Pipe) {
            self.advance(); // consume leading |

            let mut cells = Vec::new();
            loop {
                // Parse cell expression
                let cell = self.parse_expression()?;
                cells.push(cell);

                if self.check(&TokenKind::Pipe) {
                    self.advance(); // consume |
                                    // Check if this is the trailing | (end of row)
                    if self.check(&TokenKind::Newline) {
                        break;
                    }
                } else {
                    return Err(ParseError::missing_token("| after grid cell", self.current.span));
                }
            }

            self.expect(&TokenKind::Newline)?;
            rows.push(cells);

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if rows.is_empty() {
            return Err(ParseError::syntax_error_with_span(
                "Grid literal must have at least one row",
                self.current.span,
            ));
        }

        Ok(rows)
    }

    /// Parse tensor literal: tensor K: Float [d=2, h=3] ...
    fn parse_tensor_literal(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'tensor'

        // Parse name: K
        let _name = if let TokenKind::Identifier { name, .. } = &self.current.kind.clone() {
            let n = name.clone();
            self.advance();
            n
        } else {
            return Err(ParseError::unexpected_token(
                "identifier for tensor name",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Colon)?;

        // Parse dtype: Float, Int, etc.
        let dtype = if let TokenKind::Identifier { name: dt, .. } = &self.current.kind.clone() {
            let d = dt.clone();
            self.advance();
            d
        } else {
            return Err(ParseError::unexpected_token(
                "type name for tensor",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Parse dimensions: [d=2, h=3, w=4]
        self.expect(&TokenKind::LBracket)?;
        let mut dims = Vec::new();
        loop {
            if self.check(&TokenKind::RBracket) {
                break;
            }

            // Parse dim_name=value
            let dim_name = if let TokenKind::Identifier { name, .. } = &self.current.kind.clone() {
                let n = name.clone();
                self.advance();
                n
            } else {
                return Err(ParseError::unexpected_token(
                    "dimension name",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Assign)?;

            let dim_value = if let TokenKind::Integer(val) = self.current.kind {
                self.advance();
                val
            } else {
                return Err(ParseError::unexpected_token(
                    "integer for dimension size",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            dims.push((dim_name, dim_value));

            if self.check(&TokenKind::Comma) {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;

        // Optional device parameter
        let device = if self.check_ident("device") {
            self.advance(); // consume 'device'
            self.expect(&TokenKind::Assign)?;
            match &self.current.kind {
                TokenKind::String(s) => {
                    let dev = s.clone();
                    self.advance();
                    Some(dev)
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "string literal for device",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        } else {
            None
        };

        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse mode: slice or flat
        let mode = if self.check_ident("slice") {
            // Slice mode
            let slices = self.parse_tensor_slices()?;
            TensorMode::Slice(slices)
        } else if self.check_ident("default") || self.check_ident("flat") {
            // Flat mode
            let default_val = if self.check_ident("default") {
                self.advance(); // consume 'default'
                self.expect(&TokenKind::Colon)?;
                let val = self.parse_expression()?;
                self.expect(&TokenKind::Newline)?;
                Some(val)
            } else {
                None
            };

            self.expect(&TokenKind::Flat)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            let values = self.parse_grid_rows()?;

            self.expect(&TokenKind::Dedent)?;

            // Box all expressions in values and default
            let boxed_values = values
                .into_iter()
                .map(|row| row.into_iter().map(Box::new).collect())
                .collect();
            let boxed_default = default_val.map(Box::new);

            TensorMode::Flat {
                default: boxed_default,
                values: boxed_values,
            }
        } else {
            return Err(ParseError::syntax_error_with_span(
                "'slice' or 'flat' mode in tensor literal",
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Dedent)?;

        Ok(Expr::TensorLiteral {
            dtype,
            dims,
            mode: Box::new(mode),
            device,
        })
    }

    /// Parse tensor slices recursively
    fn parse_tensor_slices(&mut self) -> Result<Vec<TensorSlice>, ParseError> {
        use crate::ast::TensorSliceContent;

        let mut slices = Vec::new();

        while self.check_ident("slice") {
            self.advance(); // consume 'slice'

            // Parse dim_name=value
            let dim_name = if let TokenKind::Identifier { name, .. } = &self.current.kind.clone() {
                let n = name.clone();
                self.advance();
                n
            } else {
                return Err(ParseError::unexpected_token(
                    "dimension name",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Assign)?;

            let dim_value = if let TokenKind::Integer(val) = self.current.kind {
                self.advance();
                val
            } else {
                return Err(ParseError::unexpected_token(
                    "integer for slice index",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            // Check if nested slices or grid rows
            let content = if self.check_ident("slice") {
                let nested = self.parse_tensor_slices()?;
                TensorSliceContent::NestedSlices(nested)
            } else {
                let rows = self.parse_grid_rows()?;
                // Box all expressions in grid rows
                let boxed_rows = rows
                    .into_iter()
                    .map(|row| row.into_iter().map(Box::new).collect())
                    .collect();
                TensorSliceContent::GridRows(boxed_rows)
            };

            self.expect(&TokenKind::Dedent)?;

            slices.push(TensorSlice {
                dim_name,
                dim_value,
                content,
            });

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        Ok(slices)
    }
}

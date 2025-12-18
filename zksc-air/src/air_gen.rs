use crate::symbolic::{Op, SymbolicContext};
use icicle_babybear::field::ScalarField as Field;
use icicle_trace::{air::*, symbolic_builder::*};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

pub fn generate_trace_matrix(ctx: &SymbolicContext, num_rows: usize) -> RowMajorMatrix<Field> {
    let values_map = ctx.get_values_map();
    let num_cols = ctx.num_vars();

    if num_cols == 0 {
        return RowMajorMatrix::new(vec![], 0);
    }

    let mut trace_values = Vec::with_capacity(num_rows * num_cols);

    for row in 0..num_rows {
        for col in 0..num_cols {
            let val = values_map.get(&(row, col))
                .cloned()
                .unwrap_or(Field::from(0u32));
            trace_values.push(val);
        }
    }

    let rows_needed = num_rows.next_power_of_two();
    for _ in num_rows..rows_needed {
        for _ in 0..num_cols {
            trace_values.push(Field::from(0u32));
        }
    }

    RowMajorMatrix::new(trace_values, num_cols)
}
pub struct DynamicAIR {
    pub num_cols: usize,
    pub operations: Vec<Op>,
}

impl DynamicAIR {
    pub fn from_symbolic_context(ctx: &SymbolicContext) -> Self {
        DynamicAIR {
            num_cols: ctx.num_vars(),
            operations: ctx.get_operations(),
        }
    }
}

impl<F: icicle_core::field::Field> BaseAir<F> for DynamicAIR {
    fn width(&self) -> usize {
        self.num_cols
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for DynamicAIR {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        for op in &self.operations {
            match op {
                Op::Witness(row, _idx) => {
                    let _ = main.row_slice(*row);
                }
                Op::Constant(row, _idx, _val) => {
                    let _ = main.row_slice(*row);
                }
                Op::Add(row, a, b, result) => {
                    if let Some(row_slice) = main.row_slice(*row) {
                        let a_var = row_slice[*a].clone();
                        let b_var = row_slice[*b].clone();
                        let result_var = row_slice[*result].clone();
                        let constraint = result_var - (a_var + b_var);
                        builder.assert_zero(constraint);
                    }
                }
                Op::Mul(row, a, b, result) => {
                    if let Some(row_slice) = main.row_slice(*row) {
                        let a_var = row_slice[*a].clone();
                        let b_var = row_slice[*b].clone();
                        let result_var = row_slice[*result].clone();
                        let constraint = result_var - (a_var * b_var);
                        builder.assert_zero(constraint);
                    }
                }
                Op::Copy(src_row, src, dst_row, dst) => {
                    if src_row == dst_row {
                        if let Some(row_slice) = main.row_slice(*src_row) {
                            let src_var = row_slice[*src].clone();
                            let dst_var = row_slice[*dst].clone();
                            let constraint = dst_var - src_var;
                            builder.assert_zero(constraint);
                        }
                    } else {
                        if let (Some(src_slice), Some(dst_slice)) =
                            (main.row_slice(*src_row), main.row_slice(*dst_row)) {
                            let src_var = src_slice[*src].clone();
                            let dst_var = dst_slice[*dst].clone();
                            let constraint = dst_var - src_var;
                            builder.assert_zero(constraint);
                        }
                    }
                }
                Op::AssertZero(row, v) => {
                    if let Some(row_slice) = main.row_slice(*row) {
                        let v_var = row_slice[*v].clone();
                        builder.assert_zero(v_var);
                    }
                }
            }
        }
    }
}

pub fn extract_and_print_constraints(ctx: &SymbolicContext) {
    let air = DynamicAIR::from_symbolic_context(ctx);
    let constraints = get_symbolic_constraints::<Field, DynamicAIR>(&air, 0, 0);

    let degree_1 = constraints.iter().filter(|c| c.degree_multiple() == 1).count();
    let degree_2 = constraints.iter().filter(|c| c.degree_multiple() == 2).count();
    let degree_3plus = constraints.iter().filter(|c| c.degree_multiple() > 2).count();

    println!("Constraints: {} total ({} linear, {} quadratic{})",
             constraints.len(),
             degree_1,
             degree_2,
             if degree_3plus > 0 { format!(", {} degree 3+", degree_3plus) } else { String::new() });
}

pub fn generate_and_print_trace(ctx: &SymbolicContext, num_rows: usize) {
    let trace = generate_trace_matrix(ctx, num_rows);
    println!("Trace: {} rows × {} columns", trace.height(), trace.width());
}

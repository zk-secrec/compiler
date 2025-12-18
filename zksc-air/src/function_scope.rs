use icicle_babybear::field::ScalarField as Field;
use std::cell::RefCell;
use std::collections::HashMap;

use crate::symbolic::{Var, Op, SymbolicContext};

#[derive(Debug, Clone)]
pub struct FunctionScope {
    pub name: String,
    pub start_col: usize,      
    pub num_cols: usize,       
    pub param_count: usize,    
    pub return_count: usize,   
    pub call_count: usize,     
}

impl FunctionScope {
    pub fn new(name: String, start_col: usize, num_cols: usize, param_count: usize, return_count: usize) -> Self {
        FunctionScope {
            name,
            start_col,
            num_cols,
            param_count,
            return_count,
            call_count: 0,
        }
    }

    pub fn local_col(&self, local_idx: usize) -> usize {
        assert!(local_idx < self.num_cols, "Local variable {} out of bounds for function {}", local_idx, self.name);
        self.start_col + local_idx
    }

    pub fn param_cols(&self) -> Vec<usize> {
        (0..self.param_count).map(|i| self.local_col(i)).collect()
    }

    pub fn return_cols(&self) -> Vec<usize> {
        let return_start = self.num_cols - self.return_count;
        (0..self.return_count).map(|i| self.local_col(return_start + i)).collect()
    }
}

pub struct ScopedContext {
    inner: SymbolicContext,
    function_scopes: RefCell<HashMap<String, FunctionScope>>,
    next_function_start: RefCell<usize>,
    current_function: RefCell<Option<FunctionScope>>, 
    current_row: RefCell<usize>,  
    max_rows_used: RefCell<usize>,  
    column_remap_stack: RefCell<Vec<HashMap<usize, usize>>>,
}

impl ScopedContext {
    pub fn new() -> Self {
        ScopedContext {
            inner: SymbolicContext::new(),
            function_scopes: RefCell::new(HashMap::new()),
            next_function_start: RefCell::new(0),
            current_function: RefCell::new(None),
            current_row: RefCell::new(0),  
            max_rows_used: RefCell::new(1),
            column_remap_stack: RefCell::new(Vec::new()),
        }
    }

    fn remap_column(&self, col: usize) -> usize {
        let stack = self.column_remap_stack.borrow();
        if stack.is_empty() {
            col  
        } else {
            stack.last().unwrap().get(&col).copied().unwrap_or(col)
        }
    }

    pub fn current_row(&self) -> usize {
        *self.current_row.borrow()
    }

    pub fn num_rows(&self) -> usize {
        *self.max_rows_used.borrow()
    }

    fn allocate_row(&self) -> usize {
        let row = *self.max_rows_used.borrow();
        *self.max_rows_used.borrow_mut() += 1;
        row
    }

    fn allocate_function(&self, name: &str, num_cols: usize, param_count: usize, return_count: usize) -> FunctionScope {
        let start_col = *self.next_function_start.borrow();
        *self.next_function_start.borrow_mut() += num_cols;

        let scope = FunctionScope::new(
            name.to_string(),
            start_col,
            num_cols,
            param_count,
            return_count,
        );

        self.function_scopes.borrow_mut().insert(name.to_string(), scope.clone());
        scope
    }

    pub fn get_or_create_function_scope(&self, name: &str, num_cols: usize, param_count: usize, return_count: usize) -> FunctionScope {
        let exists = {
            self.function_scopes.borrow().contains_key(name)
        };

        if exists {
            let scope = self.function_scopes.borrow().get(name).unwrap().clone();
            assert_eq!(scope.num_cols, num_cols, "Function {} re-allocated with different column count", name);
            assert_eq!(scope.param_count, param_count, "Function {} re-allocated with different parameter count", name);
            assert_eq!(scope.return_count, return_count, "Function {} re-allocated with different return count", name);
            scope
        } else {
            self.allocate_function(name, num_cols, param_count, return_count)
        }
    }

    pub fn copy_var(&self, src: Var, dst_col: usize) -> Var {
        let dst_var = Var::new(dst_col);

        let src_row = self.inner.get_current_row();
        let dst_row = self.inner.get_current_row();

        let src_value = self.inner.get_value_at(src_row, src.index);
        self.inner.set_value_at(dst_row, dst_col, src_value);
        self.inner.operations.borrow_mut().push(Op::Copy(src_row, src.index, dst_row, dst_col));
        {
            let mut next_var = self.inner.next_var.borrow_mut();
            if dst_col >= *next_var {
                *next_var = dst_col + 1;
            }
        }

        dst_var
    }

    pub fn enter_function(&self, name: &str, num_cols: usize, params: &[Var]) -> (FunctionScope, Vec<Var>) {
        let scope = self.get_or_create_function_scope(name, num_cols, params.len(), 0);
        let param_vars: Vec<Var> = params.iter()
            .zip(scope.param_cols().iter())
            .map(|(param, &col)| self.copy_var(*param, col))
            .collect();

        (scope, param_vars)
    }

    pub fn exit_function(&self, scope: &FunctionScope, return_vars: &[Var]) -> Vec<Var> {
        let result_vars: Vec<Var> = return_vars.iter()
            .map(|ret_var| {
                let caller_col = *self.inner.next_var.borrow();
                *self.inner.next_var.borrow_mut() += 1;
                self.copy_var(*ret_var, caller_col)
            })
            .collect();

        result_vars
    }

    pub fn add_wit(&self, w: u32) {
        self.inner.add_wit(w);
    }

    pub fn witness(&self) -> Var {
        self.inner.get_wit()
    }

    pub fn add_ins(&self, w: u32) {
        self.inner.add_ins(w);
    }

    pub fn instance(&self) -> Var {
        self.inner.get_ins()
    }

    pub fn constant(&self, val: u32) -> Var {
        self.inner.constant(val)
    }

    pub fn add(&self, a: Var, b: Var) -> Var {
        let remapped_a = Var::new(self.remap_column(a.index));
        let remapped_b = Var::new(self.remap_column(b.index));
        self.inner.add(remapped_a, remapped_b)
    }

    pub fn mul(&self, a: Var, b: Var) -> Var {
        let remapped_a = Var::new(self.remap_column(a.index));
        let remapped_b = Var::new(self.remap_column(b.index));
        self.inner.mul(remapped_a, remapped_b)
    }

    pub fn assert_zero(&self, v: Var) {
        let remapped_v = Var::new(self.remap_column(v.index));
        self.inner.assert_zero(remapped_v);
    }

    pub fn get_value(&self, v: Var) -> Field {
        self.inner.get_value(v)
    }

    pub fn inner_ctx(&self) -> &SymbolicContext {
        &self.inner
    }

    pub fn print_summary(&self) {
        self.inner.print_summary();
    }

    pub fn local_var(&self, scope: &FunctionScope, local_idx: usize, value: Field) -> Var {
        let col = scope.local_col(local_idx);
        let row = self.current_row();
        self.inner.set_value_at(row, col, value);
        if col >= *self.inner.next_var.borrow() {
            *self.inner.next_var.borrow_mut() = col + 1;
        }
        Var::new(col)
    }

    pub fn begin_function_ctx(&self, name: &str, num_cols: usize, params: &[Var]) -> Vec<usize> {
        let mut scope = self.get_or_create_function_scope(name, num_cols, params.len(), 0);

        let row = scope.call_count + 1;

        if row >= *self.max_rows_used.borrow() {
            *self.max_rows_used.borrow_mut() = row + 1;
        }

        *self.current_row.borrow_mut() = row;

        self.inner.set_current_row(row);

        scope.call_count += 1;
        self.function_scopes.borrow_mut().insert(name.to_string(), scope.clone());

        let mut remap = HashMap::new();
        let param_cols: Vec<usize> = params.iter()
            .zip(scope.param_cols().iter())
            .enumerate()
            .map(|(i, (param, &col))| {
                let value = self.inner.get_value_at(0, param.index);
                self.inner.set_value_at(row, col, value);
                self.inner.operations.borrow_mut().push(Op::Copy(0, param.index, row, col));
                remap.insert(param.index, col);
                col
            })
            .collect();

        self.column_remap_stack.borrow_mut().push(remap);
        *self.current_function.borrow_mut() = Some(scope);

        param_cols
    }

    pub fn end_function_ctx(&self, name: &str, return_cols: &[usize]) -> Vec<usize> {
        let scope = self.current_function.borrow().clone()
            .expect(&format!("end_function_ctx('{}') called without begin_function_ctx", name));

        assert_eq!(scope.name, name,
                   "end_function_ctx mismatch: expected '{}', got '{}'",
                   name, scope.name);

        let func_row = self.inner.get_current_row();

        let caller_cols: Vec<usize> = return_cols.iter()
            .map(|&ret_col| {
                let remapped_ret_col = self.remap_column(ret_col);

                let caller_col = *self.inner.next_var.borrow();
                *self.inner.next_var.borrow_mut() += 1;

                let value = self.inner.get_value_at(func_row, remapped_ret_col);

                self.inner.set_value_at(0, caller_col, value);

                self.inner.operations.borrow_mut().push(Op::Copy(func_row, remapped_ret_col, 0, caller_col));

                caller_col
            })
            .collect();

        self.column_remap_stack.borrow_mut().pop()
            .expect("Column remap stack underflow - end_function_ctx without matching begin_function_ctx");

        *self.current_row.borrow_mut() = 0;
        self.inner.set_current_row(0);
        *self.current_function.borrow_mut() = None;

        caller_cols
    }

    pub fn get_local_col(&self, local_idx: usize) -> usize {
        let scope = self.current_function.borrow().clone()
            .expect("get_local_col called outside function context");
        scope.local_col(local_idx)
    }
}

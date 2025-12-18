use icicle_babybear::field::ScalarField as Field;
use std::cell::RefCell;
use std::collections::{VecDeque, HashMap};
use std::ops::{Add, Mul};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Var {
    pub index: usize,
}

impl Var {
    pub fn new(index: usize) -> Self {
        Var { index }
    }
}

#[derive(Debug, Clone)]
pub enum Op {
    Witness(usize, usize),
    Constant(usize, usize, u32),
    Add(usize, usize, usize, usize),
    Mul(usize, usize, usize, usize),
    Copy(usize, usize, usize, usize),
    AssertZero(usize, usize),
}

pub struct SymbolicContext {
    pub(crate) values: RefCell<HashMap<(usize, usize), Field>>,
    wit_stream: RefCell<VecDeque<u32>>,
    ins_stream: RefCell<VecDeque<u32>>,
    pub(crate) operations: RefCell<Vec<Op>>,
    pub(crate) next_var: RefCell<usize>,
    pub(crate) current_row: RefCell<usize>,
}

impl SymbolicContext {
    pub fn new() -> Self {
        SymbolicContext {
            values: RefCell::new(HashMap::new()),
            wit_stream: RefCell::new(VecDeque::new()),
            ins_stream: RefCell::new(VecDeque::new()),
            operations: RefCell::new(Vec::new()),
            next_var: RefCell::new(0),
            current_row: RefCell::new(0),
        }
    }

    pub fn set_current_row(&self, row: usize) {
        *self.current_row.borrow_mut() = row;
    }

    pub fn get_current_row(&self) -> usize {
        *self.current_row.borrow()
    }

    pub fn get_value_at(&self, row: usize, col: usize) -> Field {
        self.values.borrow()
            .get(&(row, col))
            .cloned()
            .unwrap_or(Field::from(0u32))
    }

    pub fn set_value_at(&self, row: usize, col: usize, value: Field) {
        self.values.borrow_mut().insert((row, col), value);
    }

    pub fn add_wit(&self, w: u32) {
        self.wit_stream.borrow_mut().push_back(w);
    }

    pub fn get_wit(&self) -> Var {
        let w = self.wit_stream.borrow_mut()
            .pop_front()
            .expect("get_wit on empty stream");

        let row = self.get_current_row();
        let idx = *self.next_var.borrow();
        *self.next_var.borrow_mut() += 1;

        self.set_value_at(row, idx, Field::from(w));
        self.operations.borrow_mut().push(Op::Witness(row, idx));

        Var::new(idx)
    }

    pub fn add_ins(&self, w: u32) {
        self.ins_stream.borrow_mut().push_back(w);
    }

    pub fn get_ins(&self) -> Var {
        let w = self.ins_stream.borrow_mut()
            .pop_front()
            .expect("get_ins on empty stream");

        let row = self.get_current_row();
        let idx = *self.next_var.borrow();
        *self.next_var.borrow_mut() += 1;

        self.set_value_at(row, idx, Field::from(w));
        self.operations.borrow_mut().push(Op::Witness(row, idx));

        Var::new(idx)
    }

    pub fn constant(&self, val: u32) -> Var {
        let row = self.get_current_row();
        let idx = *self.next_var.borrow();
        *self.next_var.borrow_mut() += 1;

        self.set_value_at(row, idx, Field::from(val));
        self.operations.borrow_mut().push(Op::Constant(row, idx, val));

        Var::new(idx)
    }

    pub fn add(&self, a: Var, b: Var) -> Var {
        let row = self.get_current_row();
        let idx = *self.next_var.borrow();
        *self.next_var.borrow_mut() += 1;
        let val = self.get_value_at(row, a.index) + self.get_value_at(row, b.index);
        self.set_value_at(row, idx, val);
        self.operations.borrow_mut().push(Op::Add(row, a.index, b.index, idx));

        Var::new(idx)
    }

    pub fn mul(&self, a: Var, b: Var) -> Var {
        let row = self.get_current_row();
        let idx = *self.next_var.borrow();
        *self.next_var.borrow_mut() += 1;
        let val = self.get_value_at(row, a.index) * self.get_value_at(row, b.index);
        self.set_value_at(row, idx, val);
        self.operations.borrow_mut().push(Op::Mul(row, a.index, b.index, idx));
        Var::new(idx)
    }

    pub fn assert_zero(&self, v: Var) {
        let row = self.get_current_row();
        let val = self.get_value_at(row, v.index);
        assert!(val == Field::from(0u32), "Assertion failed: variable {} at row {} is not zero", v.index, row);
        self.operations.borrow_mut().push(Op::AssertZero(row, v.index));
    }

    pub fn get_value(&self, v: Var) -> Field {
        let row = self.get_current_row();
        self.get_value_at(row, v.index)
    }

    pub fn get_operations(&self) -> Vec<Op> {
        self.operations.borrow().clone()
    }

    pub fn get_values_map(&self) -> HashMap<(usize, usize), Field> {
        self.values.borrow().clone()
    }

    pub fn num_vars(&self) -> usize {
        *self.next_var.borrow()
    }

    pub fn print_summary(&self) {
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SymbolicField {
    pub var: Var,
    ctx_ptr: *const SymbolicContext,
}

unsafe impl Send for SymbolicField {}
unsafe impl Sync for SymbolicField {}

impl SymbolicField {
    pub fn new(var: Var, ctx: &SymbolicContext) -> Self {
        SymbolicField {
            var,
            ctx_ptr: ctx as *const SymbolicContext,
        }
    }

    fn ctx(&self) -> &SymbolicContext {
        unsafe { &*self.ctx_ptr }
    }

    pub fn value(&self) -> Field {
        self.ctx().get_value(self.var)
    }
}
impl Add for SymbolicField {
    type Output = SymbolicField;

    fn add(self, rhs: Self) -> Self::Output {
        let result_var = self.ctx().add(self.var, rhs.var);
        SymbolicField::new(result_var, self.ctx())
    }
}

impl Mul for SymbolicField {
    type Output = SymbolicField;

    fn mul(self, rhs: Self) -> Self::Output {
        let result_var = self.ctx().mul(self.var, rhs.var);
        SymbolicField::new(result_var, self.ctx())
    }
}

impl PartialEq for SymbolicField {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl PartialEq<Field> for SymbolicField {
    fn eq(&self, other: &Field) -> bool {
        self.value() == *other
    }
}

pub trait SymbolicOps {
    fn from_u32(&self, val: u32) -> SymbolicField;
    fn witness(&self) -> SymbolicField;
}

impl SymbolicOps for SymbolicContext {
    fn from_u32(&self, val: u32) -> SymbolicField {
        let var = self.constant(val);
        SymbolicField::new(var, self)
    }

    fn witness(&self) -> SymbolicField {
        let var = self.get_wit();
        SymbolicField::new(var, self)
    }
}

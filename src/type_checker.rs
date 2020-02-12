use super::model::Model;
use super::cwf::*;
use super::lang::ast::*;

pub struct TypeChecker<T: Model> {
    model: T
}

impl<T: Model> TypeChecker<T> {
    pub fn new(model: T) -> TypeChecker<T> {
        TypeChecker { model }
    }
    pub fn check_def(&mut self, def: &Def) -> Result<Tm, String> {
        Err("oh shit waddup".to_string())
    }
}
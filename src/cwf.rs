#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ctx {
  Empty,
  Comprehension(Box<Ty>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Morph {
  Identity(Box<Ctx>),
  Initial(Box<Ctx>), // Initial morphism from <> -> G
  Weakening(Box<Ty>), // G -> G.A
  Composition(Box<Morph>, Box<Morph>), // g . f
  // f : G -> D
  // s \in Ty(G)
  // M \in Tm(fs)
  // <f, s, M> : G.s -> D
  Extension(Box<Morph>, Box<Ty>, Box<Tm>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ty {
  Subst(Box<Morph>, Box<Ty>),
  Bool(Box<Ctx>),
  Eq(Box<Tm>, Box<Tm>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Tm {
  Subst(Box<Morph>, Box<Tm>),
  Var(Box<Ty>),
  Refl(Box<Tm>),
  True(Box<Ctx>),
  False(Box<Ctx>),
  ElimBool(Box<Ty>, Box<Tm>, Box<Tm>),
}
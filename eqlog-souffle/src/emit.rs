use std::io;
use super::ast::*;
use std::collections::{HashSet, HashMap};
use super::signature::*;
use ena::unify::{UnifyValue, NoError};
use super::union_map::UnionMap;
use std::iter::once;
use itertools::Itertools;
use std::fmt::Display;
use std::io::Write;

// pub fn write_sort(sink: &mut impl io::Write, sort: &str) -> io::Result<()> {
//     write!(sink, ".type {} <: symbol\n", sort)?;
//     write!(sink, ".decl {}_equal(lhs: {}, rhs: {})\n", sort, sort, sort)?;
//     write!(sink, ".decl {}_element(x: {})\n", sort, sort)?;
//     Ok(())
// }
// 
// fn write_tuple<Iter>(sink: &mut impl io::Write, els: Iter) -> io::Result<()>
// where
//     Iter: IntoIterator,
//     Iter::Item: Display,
// {
//     let mut el_it = els.into_iter();
// 
//     write!(sink, "(")?;
//     if let Some(x) = el_it.next() {
//         write!(sink, "{}", x)?;
//     }
//     for x in el_it {
//         write!(sink, ", {}", x)?;
//     }
//     write!(sink, ")")?;
//     Ok(())
// }
// 
// pub fn write_pred(sink: &mut impl io::Write, name: &str, arity: &[String]) -> io::Result<()> {
//     write!(sink, ".decl {}", name)?;
//     write_tuple(sink, arity.iter().enumerate().map(|(i, sort)| format!("x{}: {}", i, sort)))?;
//     write!(sink, "\n")?;
//     Ok(())
// }
// 
// pub fn write_func(sink: &mut impl io::Write, name: &str, dom: &[String], cod: &str) -> io::Result<()> {
//     let dom_arg_iter = 
//         dom.iter().enumerate().map(|(i, arg_sort)| format!("x{}: {}", i, arg_sort));
// 
//     write!(sink, ".decl {}", name)?;
//     write_tuple(sink, dom_arg_iter.clone().chain(once(format!("r: {}", cod))))?;
//     write!(sink, "\n")?;
// 
//     write!(sink, ".decl {}_should_define", name)?;
//     write_tuple(sink, dom_arg_iter)?;
//     write!(sink, "\n")?;
// 
//     Ok(())
// }
// 
// #[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
// struct TermName(String);
// 
// impl UnifyValue for TermName {
//     type Error = NoError;
// 
//     fn unify_values(lhs: &Self, rhs: &Self) -> std::result::Result<Self, Self::Error> {
//         Ok(TermName(format!("{}_{}", lhs.0, rhs.0)))
//     }
// }
// 
// type TermNameMap<'a> = UnionMap<&'a Term, TermName>;
// 
// fn add_term<'a>(tm: &'a Term, term_name_map: &mut TermNameMap<'a>) {
//     use Term::*;
//     match tm {
//         Variable(var) => term_name_map.update(tm, TermName(var.to_string())).unwrap(),
//         Wildcard(None) => panic!("Unassigned wildcard index"),
//         Wildcard(Some(i)) => {
//             term_name_map.update(tm, TermName(format!("?{}", i))).unwrap();
//         },
//         Application(func_name, args) => {
//             for arg in args {
//                 add_term(arg, term_name_map);
//             }
//             term_name_map.update(tm, TermName(format!("?{}{}", func_name, term_name_map.len()))).unwrap();
//         },
//     }
// }
// 
// pub fn assign_premise_term_names<'a>(seq: &'a Sequent, signature: &Signature) -> HashMap<&'a Term, String> {
//     let mut name_map = TermNameMap::new();
// 
//     use Sequent::*;
//     match seq {
//         Implication(premise, conclusion) => {
//             premise.for_each_subterm(|tm| { add_term(tm, &mut name_map); });
//             for atom in premise.0.iter() {
//                 if let Atom::Equal(lhs, rhs) = atom {
//                     name_map.unify(lhs, rhs).unwrap();
//                 }
//             }
//         },
//         Reduction(from, to) => {
//             to.for_each_subterm(|tm| { add_term(tm, &mut name_map); });
//             from.for_each_subterm(|tm| { if tm != from { add_term(tm, &mut name_map) } });
//         },
//         ConditionalReduction(premise, from, to) => {
//             premise.for_each_subterm(|tm| { add_term(tm, &mut name_map); });
//             to.for_each_subterm(|tm| { add_term(tm, &mut name_map); });
//             from.for_each_subterm(|tm| { if tm != from { add_term(tm, &mut name_map) } });
//             for atom in premise.0.iter() {
//                 if let Atom::Equal(lhs, rhs) = atom {
//                     name_map.unify(lhs, rhs).unwrap();
//                 }
//             }
//         },
//     };
// 
//     let result: HashMap<&'a Term, String> =
//         name_map.iter()
//         .map(|(tm, TermName(name))| (tm, name))
//         .collect();
//     debug_assert_eq!(result.values().map(|s| s.as_str()).collect::<HashSet<&str>>().len(), result.len());
//     result
// }
// 
// trait SouffleAtomWrite: io::Write {
//     fn begin_atom(&mut self) -> io::Result<()>;
// }
// 
// struct SouffleAtomWriter<Writer> {
//     writer: Writer,
//     atom_num: usize,
// }
// 
// impl<Writer: io::Write> SouffleAtomWriter<Writer> {
//     fn new(writer: Writer) -> Self {
//         SouffleAtomWriter { writer, atom_num: 0 }
//     }
// }
// 
// impl<Writer: io::Write> io::Write for SouffleAtomWriter<Writer> {
//     fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
//         self.writer.write(buf)
//     }
//     fn flush(&mut self) -> io::Result<()> {
//         self.writer.flush()
//     }
// }
// 
// impl<Writer: io::Write> SouffleAtomWrite for SouffleAtomWriter<Writer> {
//     fn begin_atom(&mut self) -> io::Result<()> {
//         if self.atom_num != 0 {
//             write!(self, ", ")?;
//         }
//         self.atom_num += 1;
//         Ok(())
//     }
// }
// 
// fn write_term(sink: &mut impl SouffleAtomWrite, tm: &Term, tm_names: &HashMap<&Term, String>) -> io::Result<()> {
//     use Term::*;
// 
//     match tm {
//         Variable(_) | Wildcard(_) => (),
//         Application(func_name, args) => {
//             for arg in args {
//                 write_term(sink, arg, tm_names)?;
//             }
//             sink.begin_atom()?;
//             write!(sink, "{}", func_name)?;
//             write_tuple(sink, args.iter().chain(once(tm)).map(|tm| tm_names.get(tm).unwrap().as_str()))?;
//         },
//     }
//     Ok(())
// }
// 
// fn write_premise_atom(sink: &mut impl SouffleAtomWrite, atom: &Atom, tm_names: &HashMap<&Term, String>) -> io::Result<()> {
//     use Atom::*;
// 
//     match atom {
//         Equal(lhs, rhs) => {
//             debug_assert_eq!(tm_names.get(lhs).unwrap(), tm_names.get(rhs).unwrap());
//             write_term(sink, lhs, tm_names)?;
//             write_term(sink, rhs, tm_names)?;
//         },
//         Defined(tm, sort) => {
//             use Term::*;
//             match (tm, sort) {
//                 (_, None) | (Application(_, _), Some(_)) => { write_term(sink, tm, tm_names)?; },
//                 (Variable(_), Some(s)) | (Wildcard(_), Some(s)) => {
//                     let tm_name = tm_names.get(tm).unwrap();
//                     sink.begin_atom()?;
//                     write!(sink, "{}_member({})", s, tm_name)?;
//                 },
//             };
//         },
//         Predicate(pred_name, args) => {
//             for arg in args {
//                 write_term(sink, arg, tm_names)?;
//             }
//             sink.begin_atom()?;
//             write!(sink, "{}", pred_name)?;
//             write_tuple(sink, args.iter().map(|arg| tm_names.get(arg).unwrap().as_str()))?;
//         },
//     };
//     Ok(())
// }
// 
// fn write_conclusion_atom<'a>(sink: &mut impl SouffleAtomWrite, atom: &'a Atom, tm_sorts: &HashMap<&'a Term, String>, tm_names: &mut HashMap<&'a Term, String>) -> io::Result<()> {
//     use Atom::*;
//     use Term::*;
// 
//     match atom {
//         Equal(lhs, rhs) => {
//             match (lhs, tm_names.get(lhs), rhs, tm_names.get(rhs)) {
//                 (_, None, _, None) => panic!("Both sides of equality undefined"),
//                 (_, Some(name), undef_tm, None) |
//                 (undef_tm, None, _, Some(name)) => {
//                     let (func_name, args) = match undef_tm {
//                         Variable(_) | Wildcard(_) => panic!("Variable or wildcard was not defined in premise"),
//                         Application(func_name, args) => (func_name, args),
//                     };
// 
//                     sink.begin_atom()?;
//                     write!(sink, "{}", func_name)?;
//                     write_tuple(
//                         sink,
//                         args.iter()
//                         .map(|arg| tm_names.get(arg).unwrap().as_str())
//                         .chain(once(name.as_str()))
//                     )?;
// 
//                     tm_names.insert(undef_tm, name.to_string());
//                 },
//                 (_, Some(lhs_name), _, Some(rhs_name)) => {
//                     let sort = tm_sorts.get(lhs).unwrap();
//                     debug_assert_eq!(sort, tm_sorts.get(rhs).unwrap());
//                     sink.begin_atom()?;
//                     write!(
//                         sink,
//                         "{}_should_define({}, {})",
//                         sort,
//                         tm_names.get(lhs).unwrap(),
//                         tm_names.get(rhs).unwrap()
//                     )?;
//                 },
//             }
//         },
//         Defined(Variable(_), _) | Defined(Wildcard(_), _) => {
//             panic!("Variable or Wildcard in Define atom of conclusion")
//         },
//         Defined(Application(func_name, args), _) => {
//             sink.begin_atom()?;
//             write!(sink, "{}_should_define", func_name)?;
//             write_tuple(sink, args.iter().map(|arg| tm_names.get(arg).unwrap().as_str()))?;
//         },
//         Predicate(pred_name, args) => {
//             sink.begin_atom()?;
//             write!(sink, "{}", pred_name)?;
//             write_tuple(sink, args.iter().map(|arg| tm_names.get(arg).unwrap().as_str()))?;
//         },
//     };
//     Ok(())
// }
// 
// pub fn write_implication(
// 
// pub fn emit_sequent(seq: &Sequent, sink: &mut impl io ::Write) -> std::io::Result<()> {
//     Ok(())
// }

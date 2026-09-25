use std::collections::{BTreeMap, BTreeSet};

use super::{Element, Error, Model, RelationId};

/// A work budget for isomorphism search, including indexing the input facts.
///
/// Finite fuel estimates elementary work, accounting for input sizes, sorting,
/// refinement, and backtracking. It roughly bounds runtime, rather than counting
/// only search nodes. Units are implementation-dependent, not elapsed time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fuel {
    /// Search without a work limit.
    Infinite,
    /// Stop with [`Error::FuelExhausted`] when this work budget is insufficient.
    Finite(u64),
}

impl Fuel {
    pub(crate) fn consume(&mut self, work: u64) -> Result<(), Error> {
        match self {
            Self::Infinite => Ok(()),
            Self::Finite(remaining) => {
                if *remaining < work {
                    return Err(Error::FuelExhausted);
                }
                *remaining -= work;
                Ok(())
            }
        }
    }
}

fn tree_work(len: usize) -> u64 {
    u64::from(len.checked_ilog2().unwrap_or(0)) + 1
}

fn sort_work(len: usize) -> u64 {
    (len as u64).saturating_mul(tree_work(len))
}

/// A total, type-preserving homomorphism between two dynamic models.
///
/// Maps act on equality classes and preserve every relation, including function
/// graphs and membership. They need not be injective or reflect relations.
/// Models must have the same ordered signature. Immutable endpoint borrows keep
/// the checked assignment valid for the lifetime of the map.
#[derive(Clone, Debug)]
pub struct ModelHom<'a> {
    source: &'a Model,
    target: &'a Model,
    images: BTreeMap<Element, Element>,
}

impl<'a> ModelHom<'a> {
    /// Checks an assignment, accepting aliases in either endpoint.
    ///
    /// Every source equality class must have an image. Repeated assignments must
    /// agree modulo target equality. Returns [`Error::InvalidModelHom`] for
    /// missing or conflicting images or a relation that is not preserved.
    pub fn new(
        source: &'a Model,
        target: &'a Model,
        images: impl IntoIterator<Item = (Element, Element)>,
    ) -> Result<Self, Error> {
        check_signatures(source, target, &mut Fuel::Infinite)?;
        let mut canonical = BTreeMap::new();
        for (element, image) in images {
            let element = source.root(element)?;
            let image = target.root(image)?;
            if element.type_ != image.type_ {
                return Err(Error::TypeMismatch {
                    expected: element.type_,
                    actual: image.type_,
                });
            }
            if let Some(previous) = canonical.insert(element, image) {
                if previous != image {
                    return Err(Error::InvalidModelHom(format!(
                        "conflicting images for {element:?}"
                    )));
                }
            }
        }
        for (type_, _) in source.signature().types() {
            for element in source.elements(type_)? {
                if !canonical.contains_key(&element) {
                    return Err(Error::InvalidModelHom(format!(
                        "missing image for {element:?}"
                    )));
                }
            }
        }
        for (relation, _) in source.signature().relations() {
            let target_rows = normalized_tuples(target, relation)?;
            for row in normalized_tuples(source, relation)? {
                let image: Vec<_> = row.iter().map(|element| canonical[element]).collect();
                if !target_rows.contains(&image) {
                    return Err(Error::InvalidModelHom(format!(
                        "relation {relation:?} is not preserved at {row:?}"
                    )));
                }
            }
        }
        Ok(Self {
            source,
            target,
            images: canonical,
        })
    }

    /// Returns the identity on a model's equality classes.
    pub fn identity(model: &'a Model) -> Self {
        let images = model
            .signature()
            .types()
            .flat_map(|(type_, _)| model.elements(type_).expect("type belongs to signature"))
            .map(|element| (element, element))
            .collect();
        Self {
            source: model,
            target: model,
            images,
        }
    }

    /// Returns the source model.
    pub fn source(&self) -> &'a Model {
        self.source
    }

    /// Returns the target model.
    pub fn target(&self) -> &'a Model {
        self.target
    }

    /// Returns the canonical image of an element, accepting source aliases.
    pub fn apply(&self, element: Element) -> Result<Element, Error> {
        Ok(self.images[&self.source.root(element)?])
    }

    /// Iterates source representatives and their canonical images in ID order.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (Element, Element)> + '_ {
        self.images
            .iter()
            .map(|(&element, &image)| (element, image))
    }

    /// Composes this map with `next`.
    /// The intermediate endpoint must be the same model instance.
    pub fn then(&self, next: &Self) -> Result<Self, Error> {
        if !std::ptr::eq(self.target, next.source) {
            return Err(Error::InvalidModelHom(
                "composition requires the same intermediate model".into(),
            ));
        }
        Ok(Self {
            source: self.source,
            target: next.target,
            images: self
                .iter()
                .map(|(element, image)| (element, next.images[&image]))
                .collect(),
        })
    }

    /// Returns the inverse if this map is an isomorphism.
    /// A bijective homomorphism can fail to reflect relations and have no inverse.
    pub fn inverse(&self) -> Result<Option<Self>, Error> {
        let mut images = BTreeMap::new();
        for (element, image) in self.iter() {
            if images.insert(image, element).is_some() {
                return Ok(None);
            }
        }
        for (type_, _) in self.target.signature().types() {
            for element in self.target.elements(type_)? {
                if !images.contains_key(&element) {
                    return Ok(None);
                }
            }
        }
        // A bijection already preserves relations, so equal finite cardinalities
        // ensure that no target facts are missing from its image.
        for (relation, _) in self.source.signature().relations() {
            if normalized_tuples(self.source, relation)?.len()
                != normalized_tuples(self.target, relation)?.len()
            {
                return Ok(None);
            }
        }
        Ok(Some(Self {
            source: self.target,
            target: self.source,
            images,
        }))
    }
}

/// Finds an isomorphism between models with the same ordered signature.
///
/// Both inputs must satisfy [`Model::is_canonical`]; otherwise returns
/// [`Error::NonCanonicalModel`]. Call [`Model::canonicalize`] before searching.
/// Compares equality classes and relation tuples, ignoring element IDs and
/// evaluation bookkeeping. This does not run rules or enforce function axioms.
///
/// Returns `Ok(None)` if no isomorphism exists, or
/// [`Error::SignatureMismatch`] if signatures differ. The witness is
/// deterministic but not necessarily unique. Search uses color refinement and
/// backtracking; highly symmetric inputs can require factorial time.
/// [`Fuel::Finite`] bounds the work across preprocessing and all search branches.
/// Exhaustion returns [`Error::FuelExhausted`], not `Ok(None)`. Use
/// [`Fuel::Infinite`] for an unbounded search.
pub fn find_isomorphism<'a>(
    source: &'a Model,
    target: &'a Model,
    fuel: Fuel,
) -> Result<Option<ModelHom<'a>>, Error> {
    find_with_pairs(source, target, &[], fuel)
}

/// Finds `h: left.target() -> right.target()` with `left.then(h) = right`.
///
/// Both maps must have the same source model instance. They may identify base
/// elements, but an isomorphism exists only if they identify the same pairs.
/// Both target models must be canonicalized before constructing the maps;
/// otherwise returns [`Error::NonCanonicalModel`].
/// Exhaustion returns [`Error::FuelExhausted`]; `Ok(None)` means no compatible
/// isomorphism exists.
///
/// ```
/// use std::sync::Arc;
/// use eqlog_runtime::{
///     find_isomorphism_under, Fuel, Model, ModelHom, Signature, Type, TypeId, TypeKind,
/// };
///
/// let signature = Arc::new(Signature::new(vec![Type {
///     name: "V".into(), kind: TypeKind::Plain, parents: vec![],
/// }], vec![])?);
/// let mut base = Model::with_signature(signature.clone());
/// let a = base.new_element(TypeId(0), &[])?;
/// let b = base.new_element(TypeId(0), &[])?;
/// let mut left = base.clone();
/// left.equate(&[], a, b)?;
/// left.canonicalize();
/// let mut right = Model::with_signature(signature);
/// let c = right.new_element(TypeId(0), &[])?;
/// let to_left = ModelHom::new(&base, &left, [(a, a), (b, b)])?;
/// let to_right = ModelHom::new(&base, &right, [(a, c), (b, c)])?;
/// let iso = find_isomorphism_under(&to_left, &to_right, Fuel::Finite(100_000))?.unwrap();
/// assert_eq!(iso.apply(b)?, c);
/// assert!(iso.inverse()?.is_some());
/// # Ok::<(), eqlog_runtime::Error>(())
/// ```
pub fn find_isomorphism_under<'a>(
    left: &ModelHom<'a>,
    right: &ModelHom<'a>,
    mut fuel: Fuel,
) -> Result<Option<ModelHom<'a>>, Error> {
    if !std::ptr::eq(left.source, right.source) {
        return Err(Error::InvalidModelHom(
            "comparison under a base requires the same source model".into(),
        ));
    }
    if !left.target.is_canonical() || !right.target.is_canonical() {
        return Err(Error::NonCanonicalModel);
    }
    fuel.consume(sort_work(left.images.len()))?;
    let pairs: Vec<_> = left
        .iter()
        .map(|(element, image)| (image, right.images[&element]))
        .collect();
    find_with_pairs(left.target, right.target, &pairs, fuel)
}

fn check_signatures(source: &Model, target: &Model, fuel: &mut Fuel) -> Result<(), Error> {
    fuel.consume(1)?;
    if std::ptr::eq(source.signature(), target.signature()) {
        return Ok(());
    }
    for signature in [source.signature(), target.signature()] {
        for (_, type_) in signature.types() {
            fuel.consume(
                1u64.saturating_add(type_.name.len() as u64)
                    .saturating_add(type_.parents.len() as u64),
            )?;
        }
        for (_, relation) in signature.relations() {
            fuel.consume(
                1u64.saturating_add(relation.name.len() as u64)
                    .saturating_add(relation.parents.len() as u64)
                    .saturating_add(relation.arity.len() as u64),
            )?;
        }
    }
    if source.signature() != target.signature() {
        return Err(Error::SignatureMismatch);
    }
    Ok(())
}

fn normalized_tuples(model: &Model, relation: RelationId) -> Result<BTreeSet<Vec<Element>>, Error> {
    model
        .tuples(relation)?
        .map(|row| row.into_iter().map(|element| model.root(element)).collect())
        .collect()
}

struct Structure {
    elements: Vec<Element>,
    indices: BTreeMap<Element, usize>,
    relations: Vec<Vec<Vec<usize>>>,
    incidences: Vec<Vec<(usize, usize, usize)>>,
    refinement_work: u64,
}

impl Structure {
    fn new(model: &Model, fuel: &mut Fuel) -> Result<Self, Error> {
        let mut elements = Vec::new();
        for (type_, _) in model.signature().types() {
            let data = model.type_data(type_)?;
            fuel.consume(1 + data.new.set.len() as u64 + data.old.set.len() as u64)?;
            elements.extend(model.elements(type_)?);
        }
        fuel.consume(sort_work(elements.len()).saturating_mul(3))?;
        elements.sort_unstable();
        let indices: BTreeMap<_, _> = elements
            .iter()
            .enumerate()
            .map(|(index, &element)| (element, index))
            .collect();
        let mut relations = Vec::new();
        let mut incidences = vec![Vec::new(); elements.len()];
        for (relation, descriptor) in model.signature().relations() {
            let width = descriptor.arity.len() as u64;
            let row_work = width.saturating_add(1).saturating_mul(
                width
                    .saturating_add(1)
                    .saturating_add(tree_work(elements.len())),
            );
            fuel.consume(row_work)?;
            let data = model.relation_data(relation)?;
            data.new.table.prepay_iteration(fuel)?;
            data.old.table.prepay_iteration(fuel)?;
            let mut tuples = model.tuples(relation)?;
            let mut rows: Vec<Vec<usize>> = Vec::new();
            loop {
                fuel.consume(row_work)?;
                let Some(row) = tuples.next() else {
                    break;
                };
                rows.push(row.iter().map(|element| indices[element]).collect());
            }
            fuel.consume(sort_work(rows.len()).saturating_mul(width.saturating_add(1)))?;
            rows.sort_unstable();
            for (row_index, row) in rows.iter().enumerate() {
                for (column, &element) in row.iter().enumerate() {
                    incidences[element].push((relation.0, row_index, column));
                }
            }
            relations.push(rows);
        }
        // Prepay each refinement round by the size of its keys and comparisons,
        // so a single search node cannot hide arbitrarily large work.
        let mut refinement_work = sort_work(elements.len())
            .saturating_mul(4)
            .saturating_add(1);
        for entries in &incidences {
            let mut key_work = 1u64;
            let mut max_width = 1u64;
            for &(relation, row, _) in entries {
                let width = 3 + relations[relation][row].len() as u64;
                key_work = key_work.saturating_add(width);
                max_width = max_width.max(width);
            }
            refinement_work = refinement_work
                .saturating_add(
                    key_work.saturating_mul(tree_work(elements.len().saturating_mul(2))),
                )
                .saturating_add(sort_work(entries.len()).saturating_mul(max_width));
        }
        Ok(Self {
            elements,
            indices,
            relations,
            incidences,
            refinement_work,
        })
    }

    fn refinement_keys(&self, colors: &[usize]) -> Vec<RefinementKey> {
        self.incidences
            .iter()
            .enumerate()
            .map(|(element, incidences)| {
                let mut neighbors: Vec<_> = incidences
                    .iter()
                    .map(|&(relation, row, column)| {
                        let colors: Vec<_> = self.relations[relation][row]
                            .iter()
                            .map(|&element| colors[element])
                            .collect();
                        (relation, column, colors)
                    })
                    .collect();
                neighbors.sort_unstable();
                (colors[element], neighbors)
            })
            .collect()
    }

    fn preserves_relations(
        &self,
        target: &Self,
        images: &[usize],
        fuel: &mut Fuel,
    ) -> Result<bool, Error> {
        for (source_rows, target_rows) in self.relations.iter().zip(&target.relations) {
            let width = source_rows.first().map_or(0, Vec::len) as u64;
            fuel.consume(
                sort_work(source_rows.len())
                    .saturating_mul(width.saturating_add(1))
                    .saturating_add(1),
            )?;
            let mut mapped: Vec<Vec<_>> = source_rows
                .iter()
                .map(|row| row.iter().map(|&element| images[element]).collect())
                .collect();
            mapped.sort_unstable();
            if mapped != *target_rows {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

type RefinementKey = (usize, Vec<(usize, usize, Vec<usize>)>);

fn find_with_pairs<'a>(
    source: &'a Model,
    target: &'a Model,
    pairs: &[(Element, Element)],
    mut fuel: Fuel,
) -> Result<Option<ModelHom<'a>>, Error> {
    if !source.is_canonical() || !target.is_canonical() {
        return Err(Error::NonCanonicalModel);
    }
    check_signatures(source, target, &mut fuel)?;
    let left = Structure::new(source, &mut fuel)?;
    let right = Structure::new(target, &mut fuel)?;
    fuel.consume(left.relations.len() as u64)?;
    if left.elements.len() != right.elements.len()
        || left
            .relations
            .iter()
            .zip(&right.relations)
            .any(|(left, right)| left.len() != right.len())
    {
        return Ok(None);
    }
    fuel.consume((left.elements.len() as u64).saturating_mul(2))?;
    let mut left_colors: Vec<_> = left
        .elements
        .iter()
        .map(|element| element.type_.0)
        .collect();
    let mut right_colors: Vec<_> = right
        .elements
        .iter()
        .map(|element| element.type_.0)
        .collect();
    let mut forward = BTreeMap::new();
    let mut backward = BTreeMap::new();
    for &(element, image) in pairs {
        fuel.consume(tree_work(forward.len()).saturating_mul(2))?;
        if let Some(previous) = forward.insert(element, image) {
            if previous != image {
                return Ok(None);
            }
        }
        if let Some(previous) = backward.insert(image, element) {
            if previous != element {
                return Ok(None);
            }
        }
    }
    fuel.consume(
        (forward.len() as u64)
            .saturating_mul(tree_work(left.elements.len()))
            .saturating_mul(2),
    )?;
    for (label, (element, image)) in forward.into_iter().enumerate() {
        let color = source.signature().types().len() + label;
        left_colors[left.indices[&element]] = color;
        right_colors[right.indices[&image]] = color;
    }
    let images = search(&left, &right, left_colors, right_colors, &mut fuel)?;
    let Some(images) = images else {
        return Ok(None);
    };
    fuel.consume(sort_work(left.elements.len()))?;
    Ok(Some(ModelHom {
        source,
        target,
        images: left
            .elements
            .iter()
            .zip(images)
            .map(|(&element, image)| (element, right.elements[image]))
            .collect(),
    }))
}

fn refine_colors(
    left: &Structure,
    right: &Structure,
    left_colors: &mut Vec<usize>,
    right_colors: &mut Vec<usize>,
    fuel: &mut Fuel,
) -> Result<bool, Error> {
    loop {
        fuel.consume(left.refinement_work.saturating_add(right.refinement_work))?;
        let previous_count = left_colors.iter().copied().collect::<BTreeSet<_>>().len();
        // A shared palette makes colors comparable between the two structures.
        let mut palette = BTreeMap::new();
        let mut recolor = |key| {
            let next = palette.len();
            *palette.entry(key).or_insert(next)
        };
        *left_colors = left
            .refinement_keys(left_colors)
            .into_iter()
            .map(&mut recolor)
            .collect();
        *right_colors = right
            .refinement_keys(right_colors)
            .into_iter()
            .map(&mut recolor)
            .collect();
        let mut left_counts = vec![0; palette.len()];
        let mut right_counts = vec![0; palette.len()];
        for &color in left_colors.iter() {
            left_counts[color] += 1;
        }
        for &color in right_colors.iter() {
            right_counts[color] += 1;
        }
        if left_counts != right_counts {
            return Ok(false);
        }
        if palette.len() == previous_count {
            return Ok(true);
        }
    }
}

struct SearchBranch {
    left_colors: Vec<usize>,
    right_colors: Vec<usize>,
    element: usize,
    color: usize,
    next_color: usize,
    next_image: usize,
}

impl SearchBranch {
    fn next(&mut self, fuel: &mut Fuel) -> Result<Option<(Vec<usize>, Vec<usize>)>, Error> {
        while self.next_image < self.right_colors.len() {
            fuel.consume(1)?;
            let image = self.next_image;
            self.next_image += 1;
            if self.right_colors[image] != self.color {
                continue;
            }
            fuel.consume((self.left_colors.len() as u64).saturating_mul(2))?;
            let mut left_colors = self.left_colors.clone();
            let mut right_colors = self.right_colors.clone();
            left_colors[self.element] = self.next_color;
            right_colors[image] = self.next_color;
            return Ok(Some((left_colors, right_colors)));
        }
        Ok(None)
    }
}

fn search(
    left: &Structure,
    right: &Structure,
    mut left_colors: Vec<usize>,
    mut right_colors: Vec<usize>,
    fuel: &mut Fuel,
) -> Result<Option<Vec<usize>>, Error> {
    // Symmetric carriers can require one branch per element even when the first
    // assignment succeeds, so search depth must not consume the call stack.
    let mut branches = Vec::new();
    loop {
        if refine_colors(left, right, &mut left_colors, &mut right_colors, fuel)? {
            let mut classes = BTreeMap::<usize, Vec<usize>>::new();
            for (element, &color) in left_colors.iter().enumerate() {
                classes.entry(color).or_default().push(element);
            }
            let ambiguous = classes
                .iter()
                .filter(|(_, elements)| elements.len() > 1)
                .min_by_key(|(_, elements)| elements.len());
            if let Some((&color, elements)) = ambiguous {
                branches.push(SearchBranch {
                    left_colors,
                    right_colors,
                    element: elements[0],
                    color,
                    next_color: classes.len(),
                    next_image: 0,
                });
            } else {
                let by_color: BTreeMap<_, _> = right_colors
                    .iter()
                    .enumerate()
                    .map(|(element, &color)| (color, element))
                    .collect();
                let images: Vec<_> = left_colors.iter().map(|color| by_color[color]).collect();
                if left.preserves_relations(right, &images, fuel)? {
                    return Ok(Some(images));
                }
            }
        }
        loop {
            let Some(branch) = branches.last_mut() else {
                return Ok(None);
            };
            if let Some((next_left, next_right)) = branch.next(fuel)? {
                left_colors = next_left;
                right_colors = next_right;
                break;
            }
            branches.pop();
        }
    }
}

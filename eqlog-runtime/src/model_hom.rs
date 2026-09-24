use std::collections::{BTreeMap, BTreeSet};

use super::{Element, Error, Model, RelationId};

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
        check_signatures(source, target)?;
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
/// Compares equality classes and sets of canonical relation tuples, ignoring
/// element IDs, aliases, duplicate rows, and evaluation bookkeeping. This does
/// not run rules or enforce function axioms on unfinished models.
///
/// Returns `Ok(None)` if no isomorphism exists, or
/// [`Error::SignatureMismatch`] if signatures differ. The witness is
/// deterministic but not necessarily unique. Search uses color refinement and
/// backtracking; highly symmetric inputs can require factorial time.
pub fn find_isomorphism<'a>(
    source: &'a Model,
    target: &'a Model,
) -> Result<Option<ModelHom<'a>>, Error> {
    find_with_pairs(source, target, &[])
}

/// Finds `h: left.target() -> right.target()` with `left.then(h) = right`.
///
/// Both maps must have the same source model instance. They may identify base
/// elements, but an isomorphism exists only if they identify the same pairs.
///
/// ```
/// use std::sync::Arc;
/// use eqlog_runtime::{
///     find_isomorphism_under, Model, ModelHom, Signature, Type, TypeId, TypeKind,
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
/// let mut right = Model::with_signature(signature);
/// let c = right.new_element(TypeId(0), &[])?;
/// let to_left = ModelHom::new(&base, &left, [(a, a), (b, b)])?;
/// let to_right = ModelHom::new(&base, &right, [(a, c), (b, c)])?;
/// let iso = find_isomorphism_under(&to_left, &to_right)?.unwrap();
/// assert_eq!(iso.apply(b)?, c);
/// assert!(iso.inverse()?.is_some());
/// # Ok::<(), eqlog_runtime::Error>(())
/// ```
pub fn find_isomorphism_under<'a>(
    left: &ModelHom<'a>,
    right: &ModelHom<'a>,
) -> Result<Option<ModelHom<'a>>, Error> {
    if !std::ptr::eq(left.source, right.source) {
        return Err(Error::InvalidModelHom(
            "comparison under a base requires the same source model".into(),
        ));
    }
    let pairs: Vec<_> = left
        .iter()
        .map(|(element, image)| (image, right.images[&element]))
        .collect();
    find_with_pairs(left.target, right.target, &pairs)
}

fn check_signatures(source: &Model, target: &Model) -> Result<(), Error> {
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
}

impl Structure {
    fn new(model: &Model) -> Result<Self, Error> {
        let mut elements = Vec::new();
        for (type_, _) in model.signature().types() {
            elements.extend(model.elements(type_)?);
        }
        elements.sort_unstable();
        let indices: BTreeMap<_, _> = elements
            .iter()
            .enumerate()
            .map(|(index, &element)| (element, index))
            .collect();
        let mut relations = Vec::new();
        let mut incidences = vec![Vec::new(); elements.len()];
        for (relation, _) in model.signature().relations() {
            let rows: Vec<Vec<_>> = normalized_tuples(model, relation)?
                .into_iter()
                .map(|row| row.iter().map(|element| indices[element]).collect())
                .collect();
            for (row_index, row) in rows.iter().enumerate() {
                for (column, &element) in row.iter().enumerate() {
                    incidences[element].push((relation.0, row_index, column));
                }
            }
            relations.push(rows);
        }
        Ok(Self {
            elements,
            indices,
            relations,
            incidences,
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

    fn preserves_relations(&self, target: &Self, images: &[usize]) -> bool {
        self.relations
            .iter()
            .zip(&target.relations)
            .all(|(source_rows, target_rows)| {
                let mut mapped: Vec<Vec<_>> = source_rows
                    .iter()
                    .map(|row| row.iter().map(|&element| images[element]).collect())
                    .collect();
                mapped.sort_unstable();
                mapped == *target_rows
            })
    }
}

type RefinementKey = (usize, Vec<(usize, usize, Vec<usize>)>);

fn find_with_pairs<'a>(
    source: &'a Model,
    target: &'a Model,
    pairs: &[(Element, Element)],
) -> Result<Option<ModelHom<'a>>, Error> {
    check_signatures(source, target)?;
    let left = Structure::new(source)?;
    let right = Structure::new(target)?;
    if left.elements.len() != right.elements.len()
        || left
            .relations
            .iter()
            .zip(&right.relations)
            .any(|(left, right)| left.len() != right.len())
    {
        return Ok(None);
    }
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
    for (label, (element, image)) in forward.into_iter().enumerate() {
        let color = source.signature().types().len() + label;
        left_colors[left.indices[&element]] = color;
        right_colors[right.indices[&image]] = color;
    }
    Ok(
        search(&left, &right, left_colors, right_colors).map(|images| ModelHom {
            source,
            target,
            images: left
                .elements
                .iter()
                .zip(images)
                .map(|(&element, image)| (element, right.elements[image]))
                .collect(),
        }),
    )
}

fn search(
    left: &Structure,
    right: &Structure,
    mut left_colors: Vec<usize>,
    mut right_colors: Vec<usize>,
) -> Option<Vec<usize>> {
    loop {
        let previous_count = left_colors.iter().copied().collect::<BTreeSet<_>>().len();
        // A shared palette makes colors comparable between the two structures.
        let mut palette = BTreeMap::new();
        let mut recolor = |key| {
            let next = palette.len();
            *palette.entry(key).or_insert(next)
        };
        left_colors = left
            .refinement_keys(&left_colors)
            .into_iter()
            .map(&mut recolor)
            .collect();
        right_colors = right
            .refinement_keys(&right_colors)
            .into_iter()
            .map(&mut recolor)
            .collect();
        let mut left_counts = vec![0; palette.len()];
        let mut right_counts = vec![0; palette.len()];
        for &color in &left_colors {
            left_counts[color] += 1;
        }
        for &color in &right_colors {
            right_counts[color] += 1;
        }
        if left_counts != right_counts {
            return None;
        }
        if palette.len() == previous_count {
            break;
        }
    }
    let mut classes = BTreeMap::<usize, Vec<usize>>::new();
    for (element, &color) in left_colors.iter().enumerate() {
        classes.entry(color).or_default().push(element);
    }
    let ambiguous = classes
        .iter()
        .filter(|(_, elements)| elements.len() > 1)
        .min_by_key(|(_, elements)| elements.len());
    if let Some((&color, elements)) = ambiguous {
        let next_color = classes.len();
        for (image, &candidate_color) in right_colors.iter().enumerate() {
            if candidate_color != color {
                continue;
            }
            let mut next_left = left_colors.clone();
            let mut next_right = right_colors.clone();
            next_left[elements[0]] = next_color;
            next_right[image] = next_color;
            if let Some(images) = search(left, right, next_left, next_right) {
                return Some(images);
            }
        }
        return None;
    }
    let by_color: BTreeMap<_, _> = right_colors
        .iter()
        .enumerate()
        .map(|(element, &color)| (color, element))
        .collect();
    let images: Vec<_> = left_colors.iter().map(|color| by_color[color]).collect();
    left.preserves_relations(right, &images).then_some(images)
}

use eqlog_runtime::PrefixTree1;

eqlog_runtime::eqlog_mod!(carrier);
pub use carrier::Carrier;

pub fn new_eqlog(parents: &[Vec<usize>], members: usize) -> Carrier {
    assert!(!parents.is_empty() && members > 0);
    u32::try_from(parents.len().checked_mul(members).unwrap()).unwrap();
    let mut model = Carrier::new();
    model.enable_compact_world();
    let mut worlds = Vec::with_capacity(parents.len());
    for _ in parents {
        worlds.push(model.new_world());
    }
    for (target, sources) in parents.iter().enumerate() {
        for &source in sources {
            let morphism = model.new_world_mor();
            model.insert_world_mor_dom(morphism, worlds[source]);
            model.insert_world_mor_cod(morphism, worlds[target]);
            assert!(model.inherit_total_world_members(morphism));
        }
    }
    for world in worlds {
        for _ in 0..members {
            model.new_el(world);
        }
    }
    model
}

pub fn new_cow(vertices: usize, members: usize) -> Vec<PrefixTree1> {
    assert!(vertices > 0 && members > 0);
    u32::try_from(vertices.checked_mul(members).unwrap()).unwrap();
    let mut worlds = Vec::with_capacity(vertices);
    for owner in 0..vertices {
        let mut carrier = PrefixTree1::new();
        for origin in owner * members..(owner + 1) * members {
            carrier.insert([u32::try_from(origin).unwrap()]);
        }
        worlds.push(carrier);
    }
    worlds
}

pub fn close_cow(parents: &[Vec<usize>], worlds: &mut [PrefixTree1]) {
    // Unique paths let inherited members keep their origin as their key.
    for (owner, sources) in parents.iter().enumerate() {
        let (previous, current) = worlds.split_at_mut(owner);
        for &source in sources {
            current[0] = current[0].union(&previous[source]);
        }
    }
}

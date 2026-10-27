use super::spec::{Evaluator, Inputs, Role};
use generated::GroupJoin;

mod generated {
    include!(concat!(env!("OUT_DIR"), "/group_join.eql.rs"));
}

pub struct Native {
    model: GroupJoin,
}

impl Native {
    pub fn new(input: &Inputs) -> Self {
        let mut model = GroupJoin::new();
        model.enable_compact_world();
        let worlds: Vec<_> = (0..input.nodes.len())
            .map(|owner| {
                let world = model.new_world();
                assert_eq!(world.0 as usize, owner);
                world
            })
            .collect();
        let keys: Vec<_> = (0..input.elements.len()).map(|_| model.new_key()).collect();
        let groups: Vec<_> = (0..input.groups).map(|_| model.new_group()).collect();
        for (edge, &(source, target)) in input.edges.iter().enumerate() {
            let morphism = model.new_world_mor();
            assert_eq!(morphism.0 as usize, edge);
            model.insert_world_mor_dom(morphism, worlds[source]);
            model.insert_world_mor_cod(morphism, worlds[target]);
            assert!(model.inherit_total_world_members(morphism));
        }
        for (owner, node) in input.nodes.iter().enumerate() {
            let world = worlds[owner];
            for element in &node.local {
                let member = model.new_el(world);
                model.insert_item(world, keys[element.key as usize], member);
                match element.role {
                    Role::Spare => {}
                    Role::Left => {
                        model.insert_left(world, groups[element.group as usize], member);
                    }
                    Role::Right => {
                        model.insert_right(world, groups[element.group as usize], member);
                    }
                }
            }
        }
        Self { model }
    }
}

impl Evaluator for Native {
    type Member = u32;

    fn close(&mut self) {
        self.model.close();
    }

    fn items(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
        Box::new(
            self.model
                .iter_item()
                .map(|(world, key, element)| (world.0 as usize, key.0, element.0)),
        )
    }

    fn members(&self) -> Box<dyn Iterator<Item = (usize, u32)> + '_> {
        Box::new(
            self.model
                .iter_world_member_el()
                .map(|(world, element)| (world.0 as usize, element.0)),
        )
    }

    fn globals(&self) -> Box<dyn Iterator<Item = u32> + '_> {
        Box::new(self.model.iter_el().map(|element| element.0))
    }

    fn left(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
        Box::new(
            self.model
                .iter_left()
                .map(|(world, group, element)| (world.0 as usize, group.0, element.0)),
        )
    }

    fn right(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
        Box::new(
            self.model
                .iter_right()
                .map(|(world, group, element)| (world.0 as usize, group.0, element.0)),
        )
    }

    fn pairs(&self) -> Box<dyn Iterator<Item = (usize, u32, u32, u32)> + '_> {
        Box::new(
            self.model
                .iter_pair()
                .map(|(world, group, x, y)| (world.0 as usize, group.0, x.0, y.0)),
        )
    }

    fn images(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
        Box::new(
            self.model
                .iter_el_mor_app()
                .map(|(morphism, x, y)| (morphism.0 as usize, x.0, y.0)),
        )
    }
}

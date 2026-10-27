macro_rules! native_engine {
    ($module:ident, $source:ident, $model:ident, [$($argument:ident),*]) => {
        pub(super) mod $module {
            use super::super::spec::View;
            use super::super::{Evaluator, Inputs, SEEDS};

            eqlog_runtime::eqlog_mod!($source);
            use $source::{$model as Model, El, Key, World, WorldMor};

            pub struct Engine {
                model: Model,
                worlds: Vec<World>,
                keys: Vec<Key>,
                morphisms: Vec<WorldMor>,
            }

            impl Engine {
                pub fn construct(inputs: &Inputs, mask: u32) -> Self {
                    let mut model = Model::new();
                    model.enable_compact_world();
                    let worlds: Vec<_> = inputs
                        .jobs
                        .iter()
                        .enumerate()
                        .map(|(owner, _)| {
                            let world = model.new_world();
                            assert_eq!(world.0 as usize, owner);
                            world
                        })
                        .collect();
                    let keys: Vec<_> = (0..SEEDS as usize + inputs.jobs.len())
                        .map(|key| {
                            let value = model.new_key();
                            assert_eq!(value.0 as usize, key);
                            value
                        })
                        .collect();
                    let morphisms: Vec<_> = (1..worlds.len())
                        .map(|owner| {
                            let morphism = model.new_world_mor();
                            assert_eq!(morphism.0 as usize, owner - 1);
                            model.insert_world_mor_dom(morphism, worlds[owner - 1]);
                            model.insert_world_mor_cod(morphism, worlds[owner]);
                            assert!(model.inherit_total_world_members(morphism));
                            morphism
                        })
                        .collect();
                    let mut seeds = Vec::new();
                    for (owner, job) in inputs.jobs.iter().enumerate() {
                        let world = worlds[owner];
                        let start = if owner == 0 { 0 } else { job.output };
                        for key in start..=job.output {
                            let member = model.new_el(world);
                            model.insert_item(world, keys[key as usize], member);
                            if owner == 0 && key < SEEDS {
                                seeds.push(member);
                            }
                        }
                        model.insert_job(world, $(keys[job.$argument as usize]),*);
                    }
                    for (key, member) in seeds.into_iter().enumerate() {
                        if mask & (1 << key) != 0 {
                            model.insert_marked(worlds[0], member);
                        }
                    }
                    Self {
                        model,
                        worlds,
                        keys,
                        morphisms,
                    }
                }
            }

            impl Evaluator for Engine {
                fn close(&mut self) {
                    self.model.close();
                }
            }

            impl View for Engine {
                type Member = u32;
                fn world_count(&self) -> usize {
                    self.worlds.len()
                }
                fn item_rows(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
                    Box::new(
                        self.model
                            .iter_item()
                            .map(|(owner, key, member)| (owner.0 as usize, key.0, member.0)),
                    )
                }
                fn members(&self) -> Box<dyn Iterator<Item = (usize, u32)> + '_> {
                    Box::new(
                        self.model
                            .iter_world_member_el()
                            .map(|(owner, member)| (owner.0 as usize, member.0)),
                    )
                }
                fn global_members(&self) -> Box<dyn Iterator<Item = u32> + '_> {
                    Box::new(self.model.iter_el().map(|member| member.0))
                }
                fn marks(&self) -> Box<dyn Iterator<Item = (usize, u32)> + '_> {
                    Box::new(
                        self.model
                            .iter_marked()
                            .map(|(owner, member)| (owner.0 as usize, member.0)),
                    )
                }
                fn lookup(&self, owner: usize, key: u32) -> Option<u32> {
                    self.model
                        .item(self.worlds[owner], self.keys[key as usize])
                        .map(|member| member.0)
                }
                fn image(&self, edge: usize, source: u32) -> Option<u32> {
                    self.model
                        .el_mor_app(self.morphisms[edge], El(source))
                        .map(|member| member.0)
                }
                fn image_rows(&self) -> Box<dyn Iterator<Item = (usize, u32, u32)> + '_> {
                    Box::new(
                        self.model
                            .iter_el_mor_app()
                            .map(|(edge, source, target)| (edge.0 as usize, source.0, target.0)),
                    )
                }
            }

        }
    };
}

native_engine!(plain, single_pass_plain, SinglePassPlain, [input, output]);
native_engine!(
    equation,
    single_pass_equation,
    SinglePassEquation,
    [input, output, left, right]
);

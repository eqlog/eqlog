"""Build a separate instrumented copy of the generated ETT evaluator."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('output', type=Path)
parser.add_argument('--reuse-primary', action='store_true', help='experimental secondary-index ablation')
parser.add_argument('--allocations', action='store_true', help='count allocation traffic in a separate run')
parser.add_argument('--inputs', action='store_true', help='time published rule input views separately')
parser.add_argument('--outputs', action='store_true', help='measure output deduplication and insertion separately')
parser.add_argument('--transport', action='store_true', help='time primary edge transport by relation')
args = parser.parse_args()
ROOT = Path(__file__).resolve().parents[1]
OUT = args.output.resolve()
OUT.mkdir(parents=True, exist_ok=True)
build_result = subprocess.run(
    ['cargo', 'build', '--release', '-p', 'eqlog-ett', '--features', 'eqlog/rebuild', '--message-format=json'],
    cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE)
messages = [json.loads(line) for line in build_result.stdout.splitlines()]
build_message, = [m for m in messages if m['reason'] == 'build-script-executed'
                  and '/eqlog-ett#' in m['package_id']]
runtime_message, = [m for m in messages if m['reason'] == 'compiler-artifact'
                    and m['target']['name'] == 'eqlog_runtime']
runtime, = [Path(p) for p in runtime_message['filenames'] if p.endswith('.rlib')]
build = Path(build_message['out_dir']).parent
generated = build / 'out/eqlog-ett/src/kernel.eql.rs'
source = generated.read_text()
if 'eqlog_runtime::IndexedTable' in source:
    raise SystemExit('This instruments native kernels; compile eqlog-ett with ModelMode::Native first.')
original_hash = hashlib.sha256(source.encode()).hexdigest()
prepared_primary = '__prepare_native_index_from_primary_0' in source
cached_graph = '__morphism_graph_context.components' in source
rewrites_inherited = 'let tm_replacements' in source
strata = re.findall(r'fn (__run_stratum_\d+(?:_at)?)\(', source)
assert strata, 'No generated strata found'
scoped_strata = sum(name.endswith('_at') for name in strata)
names = []
uprooted = sorted(set(re.findall(r'self\.(\w+_uprooted)', source)))

def ident(name):
    if name not in names:
        names.append(name)
    return names.index(name)

def timer(name):
    return f'let _profile_guard = crate::profile::enter({ident(name)});'

def functions(match):
    code = match[0] + '\n' + timer(match[1])
    if match[1] == '__canonicalize_relations':
        count = ' + '.join(f'self.{field}.len()' for field in uprooted)
        code += f'\nlet merged = {count};'
        code += f'\ncrate::profile::count({ident("merged_roots")}, merged);'
        label = 'inherited_rewrites' if rewrites_inherited else 'inherited_resets'
        code += f'\ncrate::profile::count({ident(label)}, usize::from(merged > 0));'
    return code

source, fn_count = re.subn(r'\bfn (__run_stratum_\d+(?:_at)?|__transport_component_\w+|__canonicalize_relations|recompute_model_indices\w*|__prepare_native_index_(?:from_primary_)?\d+|__extend_native_index_\d+|apply_func_defs|__close_until)\([^\n]*\)[^{\n]*\{', functions, source)
assert fn_count > len(strata), 'Expected transport and canonicalization methods'

if args.inputs:
    def input_view(match):
        return (f'let {match[3]} = {{ {timer("input:" + match[2])}\n'
                f'{match[1]}\n{match[4]} }};')

    source, input_count = re.subn(
        r'(self\.__rule_input_\d+\.publish\(&self\.(\w+)\);)\n'
        r'let (input_\d+) = (self\.__rule_input_\d+\.consume_\w+[^\n]+);',
        input_view, source)
    assert input_count, 'No published rule input views found'

def rule(match):
    label = 'rule:' + match[2]
    fields = re.findall(r'&mut delta\.(new_\w+)', match[1])
    size = ' + '.join(f'delta.{f}.len()' for f in fields) or '0usize'
    return f'{{ let before = {size};\n{timer(label)}\n{match[1]}}}; {match[2]}(env);\ncrate::profile::count({ident("output:" + match[2])}, ({size}) - before); }}'

source, rule_count = re.subn(r'(let env = \w+Env \{[^}]+)\}; (\w+)\(env\);', rule, source)
assert rule_count, 'No generated rule calls found'

if args.outputs:
    def output_batch(match):
        field = match[1]
        return (f'{{ let before = delta.{field}.len();\n'
                f'{{ {timer("dedup:" + field)}\n'
                f'delta.{field}.sort_unstable(); delta.{field}.dedup(); }}\n'
                f'crate::profile::count({ident("batch:" + field)}, before);\n'
                f'crate::profile::count({ident("unique:" + field)}, delta.{field}.len());\n'
                f'{timer("insert:" + field)}\n{match[2]} }}')

    source, output_count = re.subn(
        r'delta\.(\w+)\.sort_unstable\(\);\n'
        r'delta\.\1\.dedup\(\);\n'
        r'(for \[[^\n]+ in delta\.\1\.drain\(\.\.\) \{[^\n]+\})',
        output_batch, source)
    assert output_count, 'No deduplicated relation output batches found'

if args.transport:
    def transport_block(match):
        field = re.search(r'let source = Some\(&self\.(\w+_all)\)', match[3])
        if field is None:
            raise RuntimeError('Cannot identify the primary relation in a transport block')
        return match[1] + timer('transport:' + field[1]) + '\n' + match[3]

    source, transport_count = re.subn(
        r'(if active\[(\d+)\] \{\s*\n)'
        r'([\s\S]*?\n\s*inserted\[\2\] = relation_changed;)',
        transport_block, source)
    assert transport_count, 'No selected primary transport blocks found'

edge_method = '__propagate_context_morphism_selected' if 'fn __propagate_context_morphism_selected' in source else '__propagate_context_morphism'
source, edge_count = re.subn(r'(fn (' + edge_method + r'(?:_\w*)?)\([\s\S]*?\n\) -> bool \{)', lambda m: m[1] + f'\ncrate::profile::count({ident("edge:" + m[2])}, 1);', source)
assert edge_count, 'No primary transport functions found'
graph_call = r'self\.__morphism_graph_context.components' if cached_graph else r'eqlog_runtime::morphism_components'
graph_metric = 'graph_preparation' if cached_graph else 'graph'
source, graph_count = re.subn(r'(let components = ' + graph_call + r'\([\s\S]*?\n\);)', lambda m: '{ let _profile_guard = crate::profile::enter(' + str(ident(graph_metric)) + ');\n' + m[1] + '\ncomponents };', source)
assert graph_count, 'No morphism graph preparation found'
# Preserve the binding outside the timing scope.
source = source.replace('{ let _profile_guard = crate::profile::enter(' + str(ident(graph_metric)) + ');\nlet components =', 'let components = { let _profile_guard = crate::profile::enter(' + str(ident(graph_metric)) + ');\nlet components =')

source = source.replace('propagated.push((', f'crate::profile::count({ident("transport_batches")}, 1); propagated.push((')
for condition in ['!source_delta.is_empty()', '!source_delta.is_empty() || map_deltas.iter().any(|map| !map.is_empty())', '!source_delta.is_empty() || maps_changed']:
    source = source.replace(f'if {condition} {{', f'if {condition} {{ crate::profile::count({ident("transport_changed_inputs")}, 1);')
assert source.count('self.__allocated = false;') == 1
source = source.replace('self.__allocated = false;', f'crate::profile::count({ident("allocation_round")}, 1); self.__allocated = false;')

# This optional ablation is confined to the generated profiling copy.
if args.reuse_primary:
    if prepared_primary:
        raise RuntimeError('Primary reuse is already compiled in; this ablation applies to the baseline revision')
    source, replacements = re.subn(
        r'(let mut index = self\.__native_seed_\d+\.update\(&self\.)(\w+)_own(, [^\n]+);\n\s*self\.__native_\d+_model_0\(\[\], &mut index, false\);',
        r'\1\2_all\3;', source)
    assert replacements == 7, replacements

struct = source.split('pub struct Kernel {', 1)[1].split('\n}', 1)[0]
fields = re.findall(r'^\s*(\w+): PrefixTree\d+,', struct, re.M)
sizes = '\n'.join(f'''{{
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    let mut count = 0usize;
    for row in self.{field}.iter() {{
        std::hash::Hash::hash(&row, &mut hash);
        count += 1;
    }}
    println!("rows,{{phase}},{field},{{count}},{{}}", std::hash::Hasher::finish(&hash));
}}''' for field in fields)
source += '\nimpl Kernel { pub fn profile_sizes(&self, phase: &str) {\n' + sizes + '\n} }\n'
source += '''
impl Kernel {
    pub fn profile_graph(&self) {
        let components = eqlog_runtime::morphism_components(
            self.context_mor_dom_order_1_0(), self.context_mor_cod_order_0_1(), self.context_order_0());
        let largest = components.iter().map(|c| c.objects.len()).max().unwrap_or(0);
        let internal: usize = components.iter().map(|c| c.internal.len()).sum();
        let outgoing: usize = components.iter().map(|c| c.outgoing.len()).sum();
        println!("graph,components,{}", components.len());
        println!("graph,largest,{largest}");
        println!("graph,internal,{internal}");
        println!("graph,outgoing,{outgoing}");
    }
}
'''
(OUT / 'kernel.rs').write_text(source)

checker = (ROOT / 'eqlog-ett/src/checker.rs').read_text()
assert checker.count('let declarations = syntax::parse(source)?;') == 1
assert checker.count('checker.model.close();') == 1
checker = checker.replace('let declarations = syntax::parse(source)?;', 'let _elaboration = crate::profile::enter(' + str(ident('elaboration')) + ');\nlet declarations = syntax::parse(source)?;')
checker = checker.replace('checker.model.close();', '''drop(_elaboration);
    checker.model.profile_sizes("before");
    checker.model.close();
    checker.model.profile_sizes("after");
    checker.model.profile_graph();''')
if args.allocations:
    checker = checker.replace('checker.model.close();', '''
    let (count, bytes) = crate::allocations::measure(|| checker.model.close());
    println!("allocations,{count},{bytes}");''')
(OUT / 'checker.rs').write_text(checker)

profile = r'''
use std::cell::RefCell;
use std::time::Instant;

#[derive(Clone, Default)]
struct Metric { calls: u64, inclusive: u128, exclusive: u128, count: usize }
struct State { stack: Vec<u128>, metrics: Vec<Metric> }
thread_local! { static STATE: RefCell<State> = RefCell::new(State { stack: Vec::with_capacity(16), metrics: vec![Metric::default(); NAMES.len()] }); }
pub struct Guard { id: usize, start: Instant }
pub fn enter(id: usize) -> Guard {
    STATE.with(|s| s.borrow_mut().stack.push(0));
    Guard { id, start: Instant::now() }
}
impl Drop for Guard {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed().as_nanos();
        STATE.with(|s| {
            let mut s = s.borrow_mut();
            let child = s.stack.pop().unwrap();
            if let Some(parent) = s.stack.last_mut() { *parent += elapsed; }
            let m = &mut s.metrics[self.id];
            m.calls += 1;
            m.inclusive += elapsed;
            m.exclusive += elapsed - child;
        });
    }
}
pub fn count(id: usize, n: usize) { STATE.with(|s| s.borrow_mut().metrics[id].count += n); }
pub fn reset() { STATE.with(|s| { let mut s = s.borrow_mut(); assert!(s.stack.is_empty()); s.metrics.fill(Metric::default()); }); }
pub fn dump() {
    STATE.with(|s| {
        let s = s.borrow();
        for (name, m) in NAMES.iter().zip(&s.metrics) {
            println!("metric,{name},{},{},{},{}", m.calls, m.inclusive, m.exclusive, m.count);
        }
    });
}
'''
profile += '\nconst NAMES: &[&str] = &[' + ','.join(json.dumps(n) for n in names) + '];\n'
(OUT / 'profile.rs').write_text(profile)

main = f'''
#[path = {json.dumps(str(OUT / 'kernel.rs'))}] pub mod kernel;
#[path = {json.dumps(str(OUT / 'checker.rs'))}] mod checker;
#[path = {json.dumps(str(ROOT / 'eqlog-ett/src/syntax.rs'))}] mod syntax;
#[path = {json.dumps(str(OUT / 'profile.rs'))}] mod profile;
use std::env;
use std::fs;
fn updates(m: &mut kernel::Kernel) {{
    println!("phase,no_change"); profile::reset();
    m.close(); profile::dump();
    let context = m.new_context();
    m.define_universe(context);
    println!("phase,isolated_context"); profile::reset();
    m.close(); profile::dump();
    let a = m.new_tm(context);
    let b = m.new_tm(context);
    m.close();
    m.equate_tm(context, a, b);
    println!("phase,isolated_equality"); profile::reset();
    m.close(); profile::dump();
}}
fn main() {{
    let source = env::args().skip(1).map(|p| fs::read_to_string(p).unwrap()).collect::<Vec<_>>().join("\\n");
    match checker::check(&source) {{
        Ok(mut c) => {{
            println!("checked,{{}}", c.declarations.len());
            println!("phase,initial"); profile::dump();
            if env::var_os("ETT_PROFILE_UPDATES").is_some() {{ updates(&mut c.model); }}
        }}
        Err(e) => {{ eprintln!("{{e}}"); std::process::exit(1); }}
    }}
}}
'''
(OUT / 'main.rs').write_text(main)
if args.allocations:
    assert main.count('m.close(); profile::dump();') == 3
    main = main.replace('m.close(); profile::dump();', '''
        let (count, bytes) = allocations::measure(|| m.close());
        println!("allocations,{count},{bytes}"); profile::dump();''')
    main += '#[path = ' + json.dumps(str(ROOT / 'eqlog-bench/benches/allocations.rs')) + '] mod allocations;\n'
    (OUT / 'main.rs').write_text(main)
command = ['rustc', '--edition=2021', '-C', 'opt-level=3', '-C', 'debuginfo=1', '-L', 'dependency=' + str(runtime.parent), '--extern', 'eqlog_runtime=' + str(runtime)]
for line in (build / 'output').read_text().splitlines():
    if line.startswith('cargo:rustc-link-search='):
        command += ['-L', line.split('=', 1)[1]]
    elif line.startswith('cargo:rustc-link-lib='):
        command += ['-l', line.split('=', 1)[1]]
command += [str(OUT / 'main.rs'), '-o', str(OUT / 'profile')]
metadata = {
    'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'rustc': subprocess.check_output(['rustc', '--version'], text=True).strip(),
    'generated_sha256': original_hash,
    'runtime_sha256': hashlib.sha256(runtime.read_bytes()).hexdigest(),
    'strata': len(strata),
    'model_scoped_strata': scoped_strata,
    'timed_functions': fn_count,
    'rule_groups': rule_count,
    'reuse_primary': args.reuse_primary,
    'prepared_primary': prepared_primary,
    'cached_graph': cached_graph,
    'rewrites_inherited': rewrites_inherited,
    'allocations': args.allocations,
    'inputs': args.inputs,
    'outputs': args.outputs,
    'transport': args.transport,
}
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
print('generated:', generated, 'timed functions:', fn_count, 'rules:', rule_count, 'graph sites:', graph_count, flush=True)
subprocess.run(command, check=True)

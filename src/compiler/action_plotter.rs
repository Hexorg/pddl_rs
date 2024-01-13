
use std::{io, collections::HashMap};

use enumset::__internal::EnumSetTypeRepr;
use svg::{Document, node::{Text as NodeText, element::{Group, Text, Style, Rectangle, Line, path::Data, Path}}};

use crate::{Domain, compiler::{inertia::Relationship::*, domain::ArgKind}};

use super::{ASTActionUsize, maps::Maps, PredicateUsize, inertia::Inertia};

pub fn plot_inertia_enables(domain:&Domain, inertia:&Inertia, maps:&Maps) -> io::Result<()> {
    let grid_width = (domain.actions.len() as f32).sqrt() as u8 + 1;
    let mut grid_height = (domain.actions.len() / grid_width as usize) as u8;
    if (grid_height as usize * grid_width as usize) < domain.actions.len() {
        grid_height += 1;
    }
    let plot_width:u16 = 1024;
    let plot_height:u16 = 768;
    let half_cell_width = (plot_width / grid_width as u16)/2;
    let half_cell_height = (plot_height / grid_height as u16)/2;
    println!("{}x{}", grid_width, grid_height);
    let data = PlotterData{plot_width, plot_height, grid_width, grid_height};
    let mut top_g = Group::new().set("transform", "translate(16 16)");
    let mut all_coords = Vec::new();
    for action_idx in 0..domain.actions.len() as ASTActionUsize {
        let (mut gy, mut gx) = data.top_left(action_idx);
        let (action_g, mut coords) = action_box(domain, inertia, maps, action_idx);
        gx += half_cell_width - coords.width/2;
        gy += half_cell_height - coords.height as u16 /2;
        let action_g = action_g.set("transform", format!("translate({} {})", gx, gy));
        top_g.get_children_mut().push(Box::new(action_g));
        coords.x = gx;
        coords.y = gy;
        all_coords.push(coords);
    }
    let mut links_g = Group::new();
    for from in 0..domain.actions.len() {
        for to in 0..domain.actions.len() {
            if from != to {
                let (x1, y1) = all_coords[from].provides[0];
                let (x2, y2) = all_coords[to].wants[0];
                let distance = (((x2 as f32 -x1 as f32).powf(2.0)+(y2 as f32-y1 as f32).powf(2.0)) as f32).sqrt();
                let r = (distance*10.0) as i32;
                let d = Data::new().move_to((all_coords[from].x+x1, all_coords[from].y+y1)).elliptical_arc_to((r, r, 0, 0, 0, all_coords[to].x+x2, all_coords[to].y+y2));
                for assignment in inertia.actions[from].arg_intersect(&inertia.actions[to], maps) {
                    match inertia.actions[from].classify(&inertia.actions[to], assignment.as_slice()) {
                        Enables => {
                            links_g.get_children_mut().push(Box::new(Path::new()
                            // .set("x1", (all_coords[from].x+x1).to_string())
                            // .set("y1", (all_coords[from].y+y1).to_string())
                            // .set("x2", (all_coords[to].x+x2).to_string())
                            // .set("y2", (all_coords[to].y+y2).to_string())
                            .set("d", d)
                            .set("class", "link")));
                            break;
                        },
                        Unrelated => {},
                        Disables => {},
                    }
                }
            }
        }
    }
    top_g.get_children_mut().push(Box::new(links_g));
    let document = Document::new()
        .set("width", format!("{}px", data.plot_width))
        .set("height", format!("{}px", data.plot_height))
        .set("viewbox", format!("0 0 {} {}", data.plot_width, data.plot_height))
        .add(Style::new("
            .action rect { fill: white;  stroke: black; stroke-width:3; }
            path { stroke: black; stroke-width:1; fill:none}
            path.negative { stroke:red; }
            .wants line { stroke: black; stroke-width:3; }
            .wants line.negative { stroke: red; stroke-width:3; }
            .provides line { stroke: black; stroke-width:3; }
            .provides line.negative { stroke: red; stroke-width:3; }
            line.negative { stroke: red; }
            .predicate text { display:none; }
            .predicate:hover text { display:block; }
        "))
        .add(top_g);
    svg::save("domain.svg", &document)
}

struct PlotterData {
    plot_width: u16,
    plot_height: u16,
    grid_width: u8,
    grid_height: u8
}

impl PlotterData {
    pub fn top_left(&self, action_idx:ASTActionUsize) -> (u16, u16) {
        let grid_x = (action_idx % self.grid_width as ASTActionUsize) as u8;
        let grid_y = (action_idx / self.grid_width as ASTActionUsize) as u8;
        let left = grid_x as u16 * (self.plot_width / self.grid_width as u16);
        let top = grid_y as u16 * (self.plot_height / self.grid_height as u16);
        (top, left)
    }
}

struct PredicateCoords{
    x:u16,
    y:u16,
    width:u16,
    height:u8,
    wants:Vec<(u16, u16)>,
    provides:Vec<(u16, u16)>
}
impl PredicateCoords {
    pub fn new() -> Self {
        Self { x:0, y:0, width:0, height:0, wants: Vec::new(), provides: Vec::new() }
    }
}
fn action_box(domain:&Domain, inertia:&Inertia, maps:&Maps, action_idx:ASTActionUsize) -> (Group, PredicateCoords) {
    const CHAR_WIDTH: usize = 8;
    let mut wants_spacing: usize = 16;
    let mut provides_spacing: usize = 16;
    const PRED_LEN: u8 = 32;
    let action_name = domain.actions[action_idx as usize].name().1;
    let mut width = action_name.len()*CHAR_WIDTH;
    let height:u8 = 32;
    let max_predicates = std::cmp::max(inertia.actions[action_idx as usize].precondition.len(), inertia.actions[action_idx as usize].effect.len());
    if (max_predicates+1)*wants_spacing > width {
        width = (max_predicates+1)*wants_spacing;
    } 
    
    if width > (inertia.actions[action_idx as usize].precondition.len()+1)*wants_spacing {
        wants_spacing = width / (inertia.actions[action_idx as usize].precondition.len()+1)
    }
    if width > (inertia.actions[action_idx as usize].effect.len()+1)*provides_spacing {
        provides_spacing = width / (inertia.actions[action_idx as usize].effect.len()+1)
    }
    let mut coords = PredicateCoords::new();
    coords.width = width as u16;
    coords.height = height+PRED_LEN+PRED_LEN;
    let mut wants_g = Group::new().set("class", "wants");
    let mut provides_g = Group::new().set("class", "provides");
    let positive_wants_len = inertia.actions[action_idx as usize].precondition.positive.len();
    let positive_provides_len = inertia.actions[action_idx as usize].effect.positive.len();
    for (i, p) in inertia.actions[action_idx as usize].precondition.positive.iter().enumerate() {
        let x = (i+1)*wants_spacing;
        coords.wants.push((x as u16, 0));
        wants_g.get_children_mut().push(Box::new(
        Group::new()
            .set("class", "predicate")
            .add(Line::new()
                    .set("x1", x.to_string())
                    .set("y1", "0")
                    .set("x2", x.to_string())
                    .set("y2", PRED_LEN.to_string())
                )
            .add(Text::new()
                .set("x", x.to_string())
                .set("y", "0")
                .set("dominant-baseline", "middle")
                .set("text-anchor", "middle")
                .add(NodeText::new(p.decompile(maps, None, ArgKind::ParameterIndex)))
            )));

    }
    for (i, p) in inertia.actions[action_idx as usize].precondition.negative.iter().enumerate() {
        let x = (positive_wants_len+i+1)*wants_spacing;
        coords.wants.push((x as u16, 0));
        wants_g.get_children_mut().push(Box::new(
            Group::new()
                .set("class", "predicate")
                .add(Line::new()
            .set("x1", x.to_string())
            .set("y1", "0")
            .set("x2", x.to_string())
            .set("y2", PRED_LEN.to_string())
            .set("class", "negative")
        )
        .add(Text::new()
            .set("x", x.to_string())
            .set("y", "0")
            .set("dominant-baseline", "middle")
            .set("text-anchor", "middle")
            .add(NodeText::new(format!("!{}", p.decompile(maps, None, ArgKind::ParameterIndex))))
        )));

    }
    for (i, p) in inertia.actions[action_idx as usize].effect.positive.iter().enumerate() {
        let x = (i+1)*provides_spacing;
        coords.provides.push((x as u16, PRED_LEN as u16 +PRED_LEN as u16+height as u16));
        provides_g.get_children_mut().push(Box::new(
            Group::new()
                .set("class", "predicate")
                .add(Line::new()
            .set("x1", x.to_string())
            .set("y1", (PRED_LEN+height).to_string())
            .set("x2", x.to_string())
            .set("y2", (PRED_LEN+PRED_LEN+height).to_string())
        )
        .add(Text::new()
            .set("x", x.to_string())
            .set("y", (PRED_LEN+PRED_LEN+height).to_string())
            .set("dominant-baseline", "middle")
            .set("text-anchor", "middle")
            .add(NodeText::new(p.decompile(maps, None, ArgKind::ParameterIndex)))
        )));
    }
    for (i, p) in inertia.actions[action_idx as usize].effect.negative.iter().enumerate() {
        let x = (positive_provides_len+i+1)*provides_spacing;
        coords.provides.push((x as u16, PRED_LEN as u16 +PRED_LEN as u16+height as u16));
        provides_g.get_children_mut().push(Box::new(
            Group::new()
                .set("class", "predicate")
                .add(Line::new()
            .set("x1", x.to_string())
            .set("y1", (PRED_LEN+height).to_string())
            .set("x2", x.to_string())
            .set("y2", (PRED_LEN+PRED_LEN+height).to_string())
            .set("class", "negative")
        )
        .add(Text::new()
            .set("x", x.to_string())
            .set("y", (PRED_LEN+PRED_LEN+height).to_string())
            .set("dominant-baseline", "middle")
            .set("text-anchor", "middle")
            .add(NodeText::new(format!("!{}", p.decompile(maps, None, ArgKind::ParameterIndex))))
        )));
    }
    let g = Group::new()
        .set("class", "action")
        .add(wants_g)
        .add(
        Rectangle::new()
            .set("x", "0")
            .set("y", PRED_LEN.to_string())
            .set("width", width.to_string())
            .set("height", height.to_string())
        )
        .add(Text::new()
            .set("x", (width / 2).to_string())
            .set("y", (PRED_LEN + (height / 2)).to_string())
            .set("dominant-baseline", "middle")
            .set("text-anchor", "middle")
            .add(NodeText::new(action_name))
        )
        .add(provides_g);
    (g, coords)
}

#[cfg(test)]
mod tests {
    use crate::{lib_tests::load_repo_pddl, compiler::passes::Compiler, ReportPrinter};

    use super::plot_inertia_enables;

    #[test]
    fn test_barman() {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let compiler = Compiler::new(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone());
        let c_problem = compiler.compile().unwrap_or_print_report(&sources);
        plot_inertia_enables(&domain, &c_problem.inertia, &c_problem.maps).unwrap()
    }
}
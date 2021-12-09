use std::collections::HashMap;
use nalgebra as na;

#[derive(Clone, Debug)]
pub struct Node {
    mat: na::DMatrix<i32>,
    dim: usize,
}

impl Node {
    pub fn from_vec_and_dim(vec: Vec<i32>, dim: usize) -> Self {
        Node { mat: na::DMatrix::from_vec(dim, dim, vec), dim }
    }

    pub fn apply_label(&self, label: &mut Label) -> Self {
        let mut target = self.clone();

        for i in 0..self.dim {
            target.mat.fixed_rows_mut::<1>(i).add_scalar_mut(label.jump.mat[i]);
            target.mat.fixed_columns_mut::<1>(i).add_scalar_mut(-label.jump.mat[i]);
        }

        label.set_score(self, &target);

        target
    }
}

/// Jump vector stored in the lowest non-negative form.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Jump {
    mat: na::DVector<i32>,
    dim: usize,
}

impl Jump {
    #[inline]
    pub fn new(dim: usize) -> Self {
        Jump { mat: na::DVector::zeros(dim), dim }
    }

    #[inline]
    pub fn with_slice(mut self, slice: &[i32]) -> Self {
        self.set_from_slice(slice);
        self
    }

    pub fn set_from_slice(&mut self, slice: &[i32]) {
        let mut offset = slice.iter().copied().min().unwrap_or(0);

        if offset > 0 && slice.len() < self.dim {
            offset = 0;
        }

        for (i, elt) in self.mat.iter_mut().enumerate() {
            *elt = slice.get(i).copied().unwrap_or(0) - offset;
        }
    }
}

impl From<&[i32]> for Jump {
    #[inline]
    fn from(slice: &[i32]) -> Self {
        Self::new(slice.len()).with_slice(slice)
    }
}

impl From<(&[i32], usize)> for Jump {
    #[inline]
    fn from((slice, dim): (&[i32], usize)) -> Self {
        Self::new(dim).with_slice(slice)
    }
}

impl From<&na::DVector<i32>> for Jump {
    #[inline]
    fn from(dvec: &na::DVector<i32>) -> Self {
        dvec.clone().into()
    }
}

impl From<na::DVector<i32>> for Jump {
    #[inline]
    fn from(mut dvec: na::DVector<i32>) -> Self {
        let dim = dvec.nrows();

        dvec.add_scalar_mut(-dvec.min());

        Jump { mat: dvec, dim }
    }
}

#[derive(Clone, Debug)]
pub struct Label {
    jump:  Jump,
    score: i32,
}

impl Label {
    #[inline]
    pub fn new(dim: usize) -> Self {
        Label { jump: Jump::new(dim), score: 0 }
    }

    #[inline]
    pub fn with_score(mut self, source: &Node, target: &Node) -> Self {
        self.set_score(source, target);
        self
    }

    #[inline]
    pub fn set_score(&mut self, source: &Node, target: &Node) {
        self.score = source.mat.fold(0_i32, |a, v| if v < 0 { a + 1 } else { a })
            - target.mat.fold(0_i32, |a, v| if v < 0 { a + 1 } else { a });
    }

    #[inline]
    pub fn get_jump(&self) -> &Jump {
        &self.jump
    }

    #[inline]
    pub fn get_jump_vector(&self) -> &na::DVector<i32> {
        &self.jump.mat
    }

    #[inline]
    pub fn get_score(&self) -> i32 {
        self.score
    }
}

impl<T> From<T> for Label
where
    T: Into<Jump>,
{
    #[inline]
    fn from(spec: T) -> Self {
        Label { jump: spec.into(), score: 0 }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Edge {
    pub source_pos: usize,
    pub target_pos: usize,
}

impl Edge {
    #[inline]
    pub fn new(source_pos: usize, target_pos: usize) -> Self {
        Edge { source_pos, target_pos }
    }

    #[inline]
    pub fn set(&mut self, source_pos: usize, target_pos: usize) {
        self.source_pos = source_pos;
        self.target_pos = target_pos;
    }

    #[inline]
    pub fn get(&self) -> (usize, usize) {
        (self.source_pos, self.target_pos)
    }

    #[inline]
    pub fn rewind(&mut self) {
        self.set(0, 0);
    }
}

pub trait Stepper: Iterator<Item = Jump> {}

#[allow(dead_code)]
pub struct GreedyPair {
    row:    usize,
    column: usize,
    state:  na::DMatrix<i32>,
}

impl GreedyPair {
    pub fn new(origin: Node) -> Self {
        GreedyPair { row: 0, column: 0, state: origin.mat }
    }
}

impl Iterator for GreedyPair {
    type Item = Jump;

    fn next(&mut self) -> Option<Jump> {
        // FIXME
        None
    }
}

impl Stepper for GreedyPair {}

#[derive(Clone, Debug)]
pub struct Solver {
    solutions: Vec<Label>, // nodes[0] -> nodes[pos]
    nodes:     Vec<Node>,
    edges:     HashMap<Edge, Label>,
    cursor:    Edge,
}

impl Solver {
    pub fn from_vec_and_dim(origin: Vec<i32>, dim: usize) -> Self {
        let solutions = vec![Label::new(dim)];
        let origin: Node = Node::from_vec_and_dim(origin, dim);
        let nodes = vec![origin];
        let edges = HashMap::new();
        let cursor = Edge::new(0, 0);

        Solver { solutions, nodes, edges, cursor }
    }

    #[inline]
    pub fn rewind(&mut self) {
        self.cursor.rewind();
    }

    pub fn push_jump<D>(&mut self, jump: D)
    where
        D: Into<Label>,
    {
        let mut label: Label = jump.into();
        let source_pos = self.cursor.target_pos;
        let target = self.nodes[source_pos].apply_label(&mut label);
        let source_solution = &self.solutions[source_pos];
        let target_solution = Label::from(&label.jump.mat - &source_solution.jump.mat)
            .with_score(&self.nodes[0], &target);

        for solution in &self.solutions {
            if solution.jump == target_solution.jump {
                // FIXME
            }
        }

        let target_pos = self.nodes.len();

        self.cursor.set(source_pos, target_pos);
        self.solutions.push(target_solution);
        self.nodes.push(target);
        self.edges.insert(self.cursor, label);
    }

    #[inline]
    pub fn get_origin(&self) -> &Node {
        &self.nodes[0]
    }

    #[inline]
    pub fn get_origin_matrix(&self) -> &na::DMatrix<i32> {
        &self.get_origin().mat
    }

    #[inline]
    pub fn current_source_matrix(&self) -> &na::DMatrix<i32> {
        &self.nodes[self.cursor.source_pos].mat
    }

    #[inline]
    pub fn current_target_matrix(&self) -> &na::DMatrix<i32> {
        &self.nodes[self.cursor.target_pos].mat
    }

    #[inline]
    pub fn current_jump_matrix(&self) -> na::DMatrix<i32> {
        self.current_target_matrix() - self.current_source_matrix()
    }

    #[inline]
    pub fn current_solution_matrix(&self) -> na::DMatrix<i32> {
        self.current_target_matrix() - self.get_origin_matrix()
    }

    #[inline]
    pub fn current_label(&self) -> Option<&Label> {
        self.edges.get(&self.cursor)
    }

    #[inline]
    pub fn current_solution(&self) -> &Label {
        &self.solutions[self.cursor.target_pos]
    }

    #[inline]
    pub fn get_num_solutions(&self) -> usize {
        self.solutions.len() - 1
    }

    #[inline]
    pub fn get_all_solutions(&self) -> std::slice::Iter<Label> {
        self.solutions[1..].iter()
    }

    pub fn solve(&mut self) {
        // FIXME
    }
}

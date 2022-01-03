use std::{
    io::Write,
    fs::File,
    path::{Path, PathBuf},
    collections::HashSet,
};
use tracing::error;
use whif::{WhifError, DetailedWhifError, detailed_whif_error};

pub trait Scalar:
    Copy
    + Send
    + num::Integer
    + num::Signed
    + std::ops::AddAssign
    + std::ops::SubAssign
    + std::ops::MulAssign
    + std::ops::DivAssign
    + From<i16>
    + std::str::FromStr
    + std::fmt::Display
    + std::fmt::Debug
{
}

impl Scalar for i16 {}
impl Scalar for i32 {}
impl Scalar for i64 {}

const DEFAULT_UPPER_LIMIT: i16 = 10;

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum Relation<T: Scalar> {
    Equality(T),
    Leq(T),
    Geq(T),
    Or(T, T),
    And(T, T),
    /// Codomain is empty. 
    Contradiction,
    /// Codomain is the entire integer axis.
    Unconstrained,
}

impl<T: Scalar> Relation<T> {
    pub fn from_interval(lov: T, hiv: T, infinity: T) -> Self {
        use Relation::*;

        if hiv == lov {
            Equality(hiv)
        } else if hiv < lov {
            // If two inequalities can't be satisfied jointly, at least
            // satisfy one of them: dp >= lov or dp <= hiv
            Or(lov, hiv)
        } else if hiv < infinity {
            if -lov < infinity {
                And(lov, hiv)
            } else {
                Leq(hiv)
            }
        } else if -lov < infinity {
            Geq(lov)
        } else {
            Unconstrained
        }
    }
}

// Arithmetic negation
impl<T: Scalar> std::ops::Neg for Relation<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        use Relation::*;

        match self {
            // -(ax - by) = c -> ax - by = -c
            Equality(offset) => Equality(-offset),
            // -(ax - by) <= c -> ax - by >= -c
            Leq(hiv) => Geq(-hiv),
            Geq(lov) => Leq(-lov),
            Or(lov, hiv) => Or(-hiv, -lov),
            And(lov, hiv) => And(-hiv, -lov),
            cst => cst,
        }
    }
}

// Logical negation
impl<T: Scalar> std::ops::Not for Relation<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        use Relation::*;

        match self {
            Equality(offset) => Or(offset + T::one(), offset - T::one()),
            Leq(hiv) => Geq(hiv + T::one()),
            Geq(lov) => Leq(lov - T::one()),
            Or(lov, hiv) => And(hiv + T::one(), lov - T::one()),
            And(lov, hiv) => Or(hiv + T::one(), lov - T::one()),
            Contradiction => Unconstrained,
            Unconstrained => Contradiction,
        }
    }
}

/// The only public constructor of `Constraint`s is
/// [`Problem::add_constraint`].  See its doc comments for the
/// specification of valid argument values.
///
/// Internally, the contract is to maintain the invariants:
/// `self.row_multiplier().is_positive()`, if
/// `self.column_multiplier().is_zero()` then `self.is_unary()`, and
/// `self.target_row() >= self.target_column()`.
///
/// Note that constraints projected onto the main diagonal (but not
/// over it) are allowed, albeit only temporarily.  All such elements
/// (unary constraints) should eventually be converted into
/// `Relation::Contradiction`, or `Relation::Unconstrained` with
/// domain shrinkage.
#[derive(PartialEq, Clone, Copy, Debug)]
pub struct Constraint<T: Scalar> {
    row: usize,
    col: usize,
    mur: T,
    muc: T,
    rel: Relation<T>,
}

impl<T: Scalar> Constraint<T> {
    #[inline]
    pub fn target_row(&self) -> usize {
        self.row
    }

    #[inline]
    pub fn target_column(&self) -> usize {
        self.col
    }

    #[inline]
    pub fn row_multiplier(&self) -> T {
        self.mur
    }

    #[inline]
    pub fn column_multiplier(&self) -> T {
        self.muc
    }

    #[inline]
    pub fn relation(&self) -> Relation<T> {
        self.rel
    }

    fn canonicalize(&mut self) -> Result<(), WhifError> {
        if self.row < self.col {
            let row = self.row;
            let mur = self.mur;

            self.row = self.col;
            self.col = row;
            self.mur = self.muc;
            self.muc = mur;
            self.rel = -self.rel;
        }

        if self.mur.is_zero() {
            if self.muc.is_zero() {
                return Err(WhifError::undeclared_constraint(Vec::new()))
            }
            self.row = self.col;
            self.mur = self.muc;
            self.muc = T::zero();
            if self.mur.is_negative() {
                self.mur = -self.mur;
                self.rel = -self.rel;
            }
        } else if self.muc.is_zero() {
            self.col = self.row;
            if self.mur.is_negative() {
                self.mur = -self.mur;
                self.rel = -self.rel;
            }
        } else if self.mur.is_negative() {
            self.mur = -self.mur;
            self.muc = -self.muc;
            self.rel = -self.rel;
        }

        self.simplify();

        Ok(())
    }

    // Assumes that invariants are satisfied.
    fn simplify(&mut self) {
        let gcd = self.mur.gcd(&self.muc);

        if !gcd.is_one() {
            use Relation::*;

            self.mur /= gcd;
            self.muc /= gcd;

            match self.rel {
                Equality(offset) => {
                    if offset.is_multiple_of(&gcd) {
                        self.rel = Equality(offset / gcd);
                    } else {
                        self.rel = Contradiction;
                    }
                }
                Leq(hiv) => self.rel = Leq(hiv.div_floor(&gcd)),
                Geq(lov) => self.rel = Geq(lov.div_ceil(&gcd)),
                Or(lov, hiv) => self.rel = Or(lov.div_ceil(&gcd), hiv.div_floor(&gcd)),
                And(lov, hiv) => self.rel = And(lov.div_ceil(&gcd), hiv.div_floor(&gcd)),
                _ => {}
            }
        }
    }

    #[inline]
    fn is_unary(&self) -> bool {
        self.row == self.col
    }

    #[inline]
    fn is_delta(&self) -> bool {
        self.mur == self.muc // assuming simplification
    }

    fn update_domains(
        &mut self,
        row_domain: (T, T),
        col_domain: (T, T),
    ) -> (Option<(T, T)>, Option<(T, T)>) {
        use Relation::*;

        if self.is_unary() {
            let mut multiplier = self.mur - self.muc;

            if multiplier.is_zero() {
                self.mur = T::one();
                self.muc = T::one();
            } else {
                self.mur = T::one();
                self.muc = T::zero();

                if multiplier.is_negative() {
                    multiplier = -multiplier;
                    self.rel = -self.rel;
                }
            }

            let mut domain = row_domain;

            if domain.0 <= col_domain.0 {
                domain.0 = col_domain.0;
            }

            if domain.1 >= col_domain.1 {
                domain.1 = col_domain.1;
            }

            if domain.1 < domain.0 {
                self.rel = Contradiction;
                return (None, None)
            }

            match self.rel {
                Equality(offset) => {
                    if multiplier.is_zero() {
                        self.rel = if offset.is_zero() { Unconstrained } else { Contradiction };
                        (None, None)
                    } else {
                        if offset.is_multiple_of(&multiplier) {
                            self.rel = Unconstrained;
                            let sol = offset / multiplier;
                            (Some((sol, sol)), Some((sol, sol)))
                        } else {
                            self.rel = Contradiction;
                            (None, None)
                        }
                    }
                }
                Leq(hiv) => {
                    if multiplier.is_zero() {
                        self.rel = if hiv.is_negative() { Contradiction } else { Unconstrained };
                        (None, None)
                    } else {
                        let new_hiv = hiv.div_floor(&multiplier);

                        if new_hiv < domain.0 {
                            self.rel = Contradiction;
                            (None, None)
                        } else {
                            self.rel = Unconstrained;

                            if new_hiv < domain.1 {
                                (Some((domain.0, new_hiv)), Some((domain.0, new_hiv)))
                            } else {
                                (None, None)
                            }
                        }
                    }
                }
                Geq(lov) => {
                    if multiplier.is_zero() {
                        self.rel = if lov.is_positive() { Contradiction } else { Unconstrained };
                        (None, None)
                    } else {
                        let new_lov = lov.div_ceil(&multiplier);

                        if new_lov > domain.1 {
                            self.rel = Contradiction;
                            (None, None)
                        } else {
                            self.rel = Unconstrained;

                            if new_lov > domain.0 {
                                (Some((new_lov, domain.1)), Some((new_lov, domain.1)))
                            } else {
                                (None, None)
                            }
                        }
                    }
                }
                Or(lov, hiv) => {
                    if multiplier.is_zero() {
                        self.rel = if lov.is_positive() && hiv.is_negative() {
                            Contradiction
                        } else {
                            Unconstrained
                        };
                        (None, None)
                    } else {
                        let new_hiv = hiv.div_floor(&multiplier);
                        let new_lov = lov.div_ceil(&multiplier);

                        // dp >= domain.0 and dp <= domain.1 and (dp >= new_lov or dp <= new_hiv)

                        if new_hiv < domain.0 {
                            if new_lov > domain.1 {
                                self.rel = Contradiction;
                                (None, None)
                            } else {
                                self.rel = Unconstrained;

                                if new_lov > domain.0 {
                                    (Some((new_lov, domain.1)), Some((new_lov, domain.1)))
                                } else {
                                    (None, None)
                                }
                            }
                        } else if new_lov > domain.1 {
                            self.rel = Unconstrained;

                            if new_hiv < domain.1 {
                                (Some((domain.0, new_hiv)), Some((domain.0, new_hiv)))
                            } else {
                                (None, None)
                            }
                        } else if new_lov > new_hiv {
                            self.rel = Or(new_lov, new_hiv);
                            (None, None)
                        } else {
                            self.rel = Unconstrained;
                            (None, None)
                        }
                    }
                }
                And(lov, hiv) => {
                    if multiplier.is_zero() {
                        self.rel = if lov.is_positive() || hiv.is_negative() {
                            Contradiction
                        } else {
                            Unconstrained
                        };
                        (None, None)
                    } else {
                        let new_hiv = hiv.div_floor(&multiplier);
                        let new_lov = lov.div_ceil(&multiplier);

                        // dp >= domain.0 and dp <= domain.1 and dp >= new_lov and dp <= new_hiv

                        if new_hiv < domain.0 || new_lov > domain.1 {
                            self.rel = Contradiction;
                            (None, None)
                        } else {
                            self.rel = Unconstrained;

                            if new_hiv < domain.1 {
                                if new_lov > domain.0 {
                                    (Some((new_lov, new_hiv)), Some((new_lov, new_hiv)))
                                } else {
                                    (Some((domain.0, new_hiv)), Some((domain.0, new_hiv)))
                                }
                            } else if new_lov > domain.0 {
                                (Some((new_lov, domain.1)), Some((new_lov, domain.1)))
                            } else {
                                (None, None)
                            }
                        }
                    }
                }
                _ => (None, None),
            }
        } else {
            const FIXPOINT_LOOP_GUARD: usize = 100;

            match self.rel {
                Equality(offset) => {
                    let mut row_result = row_domain;
                    let mut col_result = col_domain;

                    for _ in 0..FIXPOINT_LOOP_GUARD {
                        let new_row_result = (
                            (self.muc * col_result.0 + offset)
                                .div_ceil(&self.mur)
                                .clamp(row_domain.0, row_domain.1),
                            (self.muc * col_result.1 + offset)
                                .div_floor(&self.mur)
                                .clamp(row_domain.0, row_domain.1),
                        );
                        let new_col_result = (
                            (self.mur * new_row_result.0 - offset)
                                .div_ceil(&self.muc)
                                .clamp(col_domain.0, col_domain.1),
                            (self.mur * new_row_result.1 - offset)
                                .div_floor(&self.muc)
                                .clamp(col_domain.0, col_domain.1),
                        );

                        if row_result != new_row_result {
                            row_result = new_row_result;
                            col_result = new_col_result;
                        } else if col_result != new_col_result {
                            col_result = new_col_result;
                        } else {
                            break
                        }
                    }

                    if row_result == row_domain && col_result == col_domain {
                        (None, None)
                    } else if row_result.0 == row_result.1 && col_result.0 == col_result.1 {
                        if self.mur * row_result.0 - self.muc * col_result.0 == offset {
                            self.rel = Unconstrained;
                            (Some(row_result), Some(col_result))
                        } else {
                            self.rel = Contradiction;
                            (None, None)
                        }
                    } else {
                        (Some(row_result), Some(col_result))
                    }
                }
                _ => {
                    // Let the actual solver do the job...
                    (None, None)
                }
            }
        }
    }

    fn apply_substitutions(
        &mut self,
        row_sub: Option<Substitution<T>>,
        col_sub: Option<Substitution<T>>,
    ) {
        use Relation::*;

        if self.is_delta() {
            let row_sub = row_sub.unwrap_or(Substitution::new(self.row));
            let col_sub = col_sub.unwrap_or(Substitution::new(self.col));
            let row_mul = row_sub.multiplier;
            let col_mul = col_sub.multiplier;
            let offset = row_sub.offset - col_sub.offset;

            if row_sub.target >= col_sub.target {
                self.row = row_sub.target;
                self.col = col_sub.target;
                self.mur = row_mul;
                self.muc = col_mul;
            } else {
                self.row = col_sub.target;
                self.col = row_sub.target;
                self.mur = col_mul;
                self.muc = row_mul;
            }

            match self.rel {
                Leq(hiv) => {
                    // sol_row - sol_col <= hiv -> row_mul * sol_row' - col_mul * sol_col' <= hiv - offset
                    if row_sub.target >= col_sub.target {
                        self.rel = Leq(hiv - offset);
                    } else {
                        self.rel = Geq(offset - hiv);
                    }
                }
                Geq(lov) => {
                    // sol_row - sol_col >= lov -> row_mul * sol_row' - col_mul * sol_col' >= lov - offset
                    if row_sub.target >= col_sub.target {
                        self.rel = Geq(lov - offset);
                    } else {
                        self.rel = Leq(offset - lov);
                    }
                }
                Or(lov, hiv) => {
                    if row_sub.target >= col_sub.target {
                        self.rel = Or(lov - offset, hiv - offset);
                    } else {
                        self.rel = Or(offset - hiv, offset - lov);
                    }
                }
                And(lov, hiv) => {
                    if row_sub.target >= col_sub.target {
                        self.rel = And(lov - offset, hiv - offset);
                    } else {
                        self.rel = And(offset - hiv, offset - lov);
                    }
                }
                _ => {}
            }

            self.simplify();

        } else {
            // FIXME non-delta substitution
        }
    }
}

impl<T: Scalar> std::fmt::Display for Constraint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Relation::*;

        if self.is_delta() {
            let Constraint { row, col, rel, .. } = *self;

            match rel {
                Equality(offset) => {
                    if offset.is_zero() {
                        write!(f, "sol_{} == sol_{}", row, col)
                    } else {
                        write!(f, "sol_{} == sol_{} + {}", row, col, offset)
                    }
                }
                Leq(hiv) => write!(f, "sol_{} - sol_{} <= {}", row, col, hiv),
                Geq(lov) => write!(f, "sol_{} - sol_{} >= {}", row, col, lov),
                Or(lov, hiv) => write!(
                    f,
                    "sol_{} - sol_{} >= {} \\/ sol_{} - sol_{} <= {}",
                    row, col, lov, row, col, hiv
                ),
                And(lov, hiv) => write!(
                    f,
                    "sol_{} - sol_{} >= {} /\\ sol_{} - sol_{} <= {}",
                    row, col, lov, row, col, hiv
                ),
                Contradiction => {
                    if row == col {
                        write!(f, "~sol_{}", row)
                    } else {
                        write!(f, "sol_{} _|_ sol_{}", row, col)
                    }
                }
                Unconstrained => write!(f, "sol_{} T sol_{}", row, col),
            }
        } else {
            #[inline]
            fn fmt_sol<T: Scalar>(
                f: &mut std::fmt::Formatter,
                mlt: T,
                idx: usize,
            ) -> std::fmt::Result {
                if mlt.is_one() {
                    write!(f, "sol_{}", idx)
                } else {
                    write!(f, "{} * sol_{}", mlt, idx)
                }
            }

            #[inline]
            fn fmt_bisol<T: Scalar>(
                f: &mut std::fmt::Formatter,
                mur: T,
                row: usize,
                muc: T,
                col: usize,
            ) -> std::fmt::Result {
                fmt_sol(f, mur, row)?;
                if muc.is_positive() {
                    write!(f, " - ")?;
                    fmt_sol(f, muc, col)
                } else {
                    write!(f, " + ")?;
                    fmt_sol(f, -muc, col)
                }
            }

            let Constraint { row, col, mur, muc, rel } = *self;

            match rel {
                Equality(offset) => {
                    if offset.is_zero() {
                        fmt_sol(f, mur, row)?;
                        write!(f, " == ")?;
                        fmt_sol(f, muc, col)
                    } else {
                        fmt_sol(f, mur, row)?;
                        write!(f, " == ")?;
                        fmt_sol(f, muc, col)?;
                        write!(f, " + {}", offset)
                    }
                }
                Leq(hiv) => {
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " <= {}", hiv)
                }
                Geq(lov) => {
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " >= {}", lov)
                }
                Or(lov, hiv) => {
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " >= {} \\/ ", lov)?;
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " <= {}", hiv)
                }
                And(lov, hiv) => {
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " >= {} /\\ ", lov)?;
                    fmt_bisol(f, mur, row, muc, col)?;
                    write!(f, " <= {}", hiv)
                }
                Contradiction => {
                    if row == col {
                        write!(f, "~sol_{}", row)
                    } else {
                        write!(f, "sol_{} _|_ sol_{}", row, col)
                    }
                }
                Unconstrained => write!(f, "sol_{} T sol_{}", row, col),
            }
        }
    }
}

// sol_source = sol_target * multiplier + offset
#[derive(PartialEq, Clone, Copy, Debug)]
pub struct Substitution<T: Scalar> {
    target:     usize,
    multiplier: T,
    offset:     T,
}

impl<T: Scalar> Substitution<T> {
    #[inline]
    fn new(target: usize) -> Self {
        Substitution { target, multiplier: T::one(), offset: T::zero() }
    }

    #[inline]
    fn with_offset(mut self, offset: T) -> Self {
        self.offset = offset;
        self
    }
}

/// Linear binary constraint satisfaction problem over integers.
///
/// A `blint::Problem` of dimension *n* is a CSP that may be reduced
/// so that it consists of *n* variables with domains given as finite
/// intervals of ℤ (set of integers), and *m* constraints, such that
/// each constraint is represented by
///
/// - a linear function of exactly two of the variables, and
///
/// - a subset of ℤ, called a *codomain* of that constraint.
///
/// Consequently, a constraint represented by a function *f* and a
/// codomain ***C*** is a binary relation containing all pairs of
/// integers from the corresponding domains on which *f* evaluates to
/// an element of ***C***.  In other words, ***C*** is the (given)
/// codomain of the restriction of *f* to the set of (unknown)
/// solutions of that single constraint.
///
/// For practical reasons, the only valid codomain of a blint
/// constraint is the union of a small set &mdash; of cardinality
/// bounded by a compile time parameter &mdash; of disjoint, possibly
/// infinite intervals of ℤ.  Furthermore, no two constraints of a
/// reduced blint problem may share both variables, hence *m* &leq;
/// (*n*-1)<sup>2</sup>.
///
/// ***Implementation details.***
///
/// The invariant `constraints[row].len() == row` is maintained for
/// every `row`.  In particular, the main diagonal is excluded, so
/// that the original set of constraints never contains a unary
/// element, i.e. the one with `row == col`.  However some constraints
/// may eventually be projected onto the main diagonal by
/// substitution, and later removed.
#[derive(Clone, Debug)]
pub struct Problem<T: Scalar> {
    domains:       Vec<(T, T)>,
    constraints:   Vec<Vec<Option<Constraint<T>>>>,
    substitutions: Vec<Option<Substitution<T>>>,
    mergeouts:     HashSet<(usize, usize)>,
    verbosity:     u32,
}

impl<T: Scalar> Problem<T> {
    #[inline]
    pub fn get_dimension(&self) -> usize {
        self.domains.len()
    }

    /// This is the only public constructor of `Constraint`s.
    ///
    /// Valid argument values must satisfy
    ///
    /// - `row < Problem::get_dimension()`,
    /// - `!(row_multiplier.is_zero() && col_multiplier.is_zero())`
    ///
    /// &mdash; binding an undeclared variable or adding a nullary
    /// constraint is an error.  Unary constraint is valid as input,
    /// but it is transformed into a restriction of variable's domain.
    pub fn add_constraint(
        &mut self,
        row: usize,
        col: usize,
        mut row_multiplier: T,
        mut col_multiplier: T,
        rel: Relation<T>,
    ) -> Result<(), WhifError> {
        if row >= self.get_dimension() {
            return Err(WhifError::undeclared_variable(row))
        }

        let mut cst = Constraint { row, col, mur: row_multiplier, muc: col_multiplier, rel };
        cst.canonicalize()?;

        if cst.is_unary() {
            if let Some(domain) = cst.update_domains(self.domains[row], self.domains[row]).0 {
                self.domains[row] = domain;
            }

            self.constraints[row][col] = Some(cst);
        } else {
            match cst.rel {
                Relation::Equality(mut offset) => {
                    if cst.is_delta() {
                        let mut target = col;

                        while let Some(next_sub) = self.substitutions[target] {
                            target = next_sub.target;
                            offset += next_sub.offset;
                        }

                        self.constraints[row][col] = None;
                        self.substitutions[row] =
                            Some(Substitution { target, multiplier: T::one(), offset });
                    } else {
                        // FIXME non-delta substitution
                        self.constraints[row][col] = None;
                    }
                }
                Relation::Unconstrained => {
                    self.constraints[row][col] = None;
                }
                _ => {
                    self.constraints[row][col] = Some(cst);
                }
            }
        }

        Ok(())
    }

    #[inline]
    pub fn get_constraint(&self, row: usize, col: usize) -> Option<Constraint<T>> {
        if row > col && row < self.constraints.len() {
            self.constraints[row][col]
        } else {
            None
        }
    }

    fn preprocess(&mut self) {
        self.propagate_substitutions();
        self.shrink_domains();
        self.remove_unconstrained();
        self.merge_constraints();
        self.sweep_constraints();
    }

    fn propagate_substitutions(&mut self) {
        for (source, sub) in self.substitutions.iter().enumerate() {
            if let Some(sub) = *sub {
                for maybe_cst in self.constraints[source].iter_mut() {
                    if let Some(cst) = maybe_cst {
                        cst.apply_substitutions(Some(sub), self.substitutions[cst.col]);
                    }
                }
            }
        }

        for row in 0..self.constraints.len() {
            for col in 0..row {
                if let Some(cst) = &mut self.constraints[row][col] {
                    let sub = &self.substitutions[cst.col];

                    if sub.is_some() {
                        cst.apply_substitutions(None, *sub);
                    }
                }
            }
        }
    }

    fn shrink_domains(&mut self) {
        // FIXME
        let dim = self.constraints.len();

        for row in 0..dim {
            let row_dom = self.domains[row];

            for col in 0..row {
                if let Some(cst) = &mut self.constraints[row][col] {
                    let (new_row_dom, new_col_dom) = cst.update_domains(row_dom, self.domains[col]);

                    if let Some(dom) = new_row_dom {
                        self.domains[row] = dom;
                    }
                    if let Some(dom) = new_col_dom {
                        self.domains[col] = dom;
                    }
                }
            }
        }
    }

    fn remove_unconstrained(&mut self) {
        for row in 0..self.constraints.len() {
            for col in 0..row {
                match self.constraints[row][col] {
                    Some(Constraint { rel: Relation::Unconstrained, .. }) => {
                        self.constraints[row][col] = None;
                    }
                    _ => {}
                }
            }
        }
    }

    fn merge_constraints(&mut self) {
        let dim = self.constraints.len();

        for row in 0..dim {
            for col in 0..row {
                if let Some(Constraint { row: actual_row, col: actual_col, rel, .. }) =
                    self.constraints[row][col]
                // FIXME multipliers
                {
                    if actual_row != row || actual_col != col {
                        if (actual_row > actual_col
                            && self.constraints[row][col]
                                == self.constraints[actual_row][actual_col])
                            || (actual_row < actual_col
                                && self.constraints[row][col]
                                    == self.constraints[actual_col][actual_row])
                        {
                            self.constraints[row][col] = None;
                            self.mergeouts.insert((row, col));
                        } else {
                            use Relation::*;

                            // FIXME
                            match rel {
                                Leq(hiv) => {}
                                Geq(lov) => {}
                                Or(lov, hiv) => {}
                                And(lov, hiv) => {}
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
    }

    fn sweep_constraints(&mut self) {
        for row in 0..self.constraints.len() {
            for col in 0..row {
                if let Some(Constraint { ref mut rel, .. }) = self.constraints[row][col] {
                    // FIXME multipliers
                    use Relation::*;

                    match *rel {
                        Or(lov, hiv) => {
                            if lov <= hiv + T::one() {
                                self.constraints[row][col] = None;
                            }
                        }
                        And(lov, hiv) => {
                            if lov > hiv {
                                *rel = Contradiction;
                            }
                        }
                        Unconstrained => {
                            self.constraints[row][col] = None;
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Solver<T: Scalar> {
    upper_limit:       T,
    lower_limit:       Option<T>,
    max_solutions:     u32,
    path_to_minizinc:  Option<PathBuf>,
    path_to_flatfile:  Option<PathBuf>,
    path_to_pathsfile: Option<PathBuf>,
    path_to_capture:   Option<PathBuf>,
    verbosity:         u32,
}

impl<T: 'static + Scalar> Solver<T> {
    const DEFAULT_PATH_TO_MINIZINC: &'static str = "../tools/MiniZincIDE/bin/";

    pub fn new() -> Self {
        Solver {
            upper_limit:       DEFAULT_UPPER_LIMIT.into(),
            lower_limit:       None,
            max_solutions:     1,
            path_to_minizinc:  None,
            path_to_flatfile:  None,
            path_to_pathsfile: None,
            path_to_capture:   None,
            verbosity:         0,
        }
    }

    pub fn with_upper_limit(mut self, upper_limit: T) -> Result<Self, WhifError> {
        self.set_upper_limit(upper_limit)?;
        Ok(self)
    }

    pub fn with_lower_limit(mut self, lower_limit: T) -> Result<Self, WhifError> {
        self.set_lower_limit(lower_limit)?;
        Ok(self)
    }

    pub fn with_max_solutions(mut self, max_solutions: u32) -> Self {
        self.set_max_solutions(max_solutions);
        self
    }

    pub fn with_minizinc<P: AsRef<Path>>(mut self, path: P) -> Result<Self, WhifError> {
        self.set_minizinc(path)?;
        Ok(self)
    }

    pub fn with_flatfile<P: AsRef<Path>>(mut self, path: P) -> Result<Self, WhifError> {
        self.set_flatfile(path)?;
        Ok(self)
    }

    pub fn with_capture<P: AsRef<Path>>(mut self, path: P) -> Result<Self, WhifError> {
        self.set_capture(path)?;
        Ok(self)
    }

    pub fn with_verbosity(mut self, verbosity: u32) -> Self {
        self.verbosity = verbosity;
        self
    }

    pub fn set_upper_limit(&mut self, upper_limit: T) -> Result<(), WhifError> {
        if let Some(lower_limit) = self.lower_limit {
            if upper_limit < lower_limit {
                return Err(WhifError::domain(None))
            }
        } else if upper_limit.is_negative() {
            return Err(WhifError::domain(None))
        }

        self.upper_limit = upper_limit;

        Ok(())
    }

    pub fn set_lower_limit(&mut self, lower_limit: T) -> Result<(), WhifError> {
        if lower_limit > self.upper_limit {
            Err(WhifError::domain(None))
        } else {
            self.lower_limit = Some(lower_limit);

            Ok(())
        }
    }

    #[inline]
    pub fn set_max_solutions(&mut self, max_solutions: u32) {
        self.max_solutions = max_solutions;
    }

    pub fn set_minizinc<P: AsRef<Path>>(&mut self, path: P) -> Result<(), WhifError> {
        let path = path.as_ref();

        if std::fs::metadata(path)?.is_dir() {
            self.path_to_minizinc = Some(path.to_path_buf());

            Ok(())
        } else {
            Err(std::io::Error::from(std::io::ErrorKind::NotADirectory).into())
        }
    }

    pub fn set_flatfile<P: AsRef<Path>>(&mut self, path: P) -> Result<(), WhifError> {
        let path = path.as_ref();

        if std::fs::metadata(path).map(|metadata| metadata.is_file()).unwrap_or(true) {
            if path.file_name().is_some() {
                self.path_to_flatfile = Some(path.to_path_buf());
                self.path_to_pathsfile = Some(path.with_extension("paths"));

                Ok(())
            } else {
                Err(WhifError::std_io(format!("File name missing in {:?}", path)))
            }
        } else {
            Err(std::io::Error::from(std::io::ErrorKind::IsADirectory).into())
        }
    }

    pub fn set_capture<P: AsRef<Path>>(&mut self, path: P) -> Result<(), WhifError> {
        let path = path.as_ref();

        if std::fs::metadata(path).map(|metadata| metadata.is_file()).unwrap_or(true) {
            self.path_to_capture = Some(path.to_path_buf());

            Ok(())
        } else {
            Err(std::io::Error::from(std::io::ErrorKind::IsADirectory).into())
        }
    }

    #[inline]
    pub fn get_upper_limit(&self) -> T {
        self.upper_limit
    }

    #[inline]
    pub fn get_lower_limit(&self) -> T {
        self.lower_limit.unwrap_or_else(|| -self.upper_limit)
    }

    pub fn get_problem(&self, dim: usize) -> Problem<T> {
        let domains = [(self.get_lower_limit(), self.upper_limit)].repeat(dim);
        let constraints = (0..dim).map(|row| [None].repeat(row + 1)).collect();
        let substitutions = [None].repeat(dim);
        let mergeouts = HashSet::new();
        let verbosity = self.verbosity;

        Problem { domains, constraints, substitutions, mergeouts, verbosity }
    }

    fn pipeout(
        pipe: &mut std::process::ChildStdin,
        capture: Option<&mut File>,
        mut line: String,
        verbosity: u32,
    ) {
        if line.starts_with('%') {
            if verbosity > 3 {
                println!("{}", line);
            }
        } else {
            if verbosity > 2 {
                println!("{}", line);
            }
            pipe.write_all(line.as_bytes()).expect("Failed to write to MiniZinc solver");
        }

        if let Some(capture) = capture {
            line.push('\n');

            let _ = capture.write_all(line.as_bytes());
        }
    }

    pub fn solve(&mut self, mut problem: Problem<T>) -> Result<(Vec<Vec<T>>, String), WhifError>
    where
        <T as std::str::FromStr>::Err: std::fmt::Debug,
    {
        problem.preprocess();

        let this = self.clone();

        if self.path_to_minizinc.is_none() {
            self.set_minizinc(Self::DEFAULT_PATH_TO_MINIZINC)?;
        }

        let minizinc_path = self
            .path_to_minizinc
            .as_ref()
            .map_or_else(|| PathBuf::from("minizinc"), |path| path.join("minizinc"));

        let mut command = std::process::Command::new(&minizinc_path);

        command
            .arg("--soln-sep")
            .arg("")
            .arg("--num-solutions")
            .arg(format!("{}", self.max_solutions));

        if let Some(path_to_flatfile) = self.path_to_flatfile.as_ref() {
            command.arg("--no-optimize").arg("--fzn").arg(path_to_flatfile);

            if let Some(path_to_pathsfile) = self.path_to_pathsfile.as_ref() {
                command.arg("--output-paths-to-file").arg(path_to_pathsfile);
            }
            // FIXME optional postprocessing:
            // findMUS --soft-defines --depth fzn --output-json <path_to_flatfile>
        }

        let mut command = command
            .arg("-")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .map_err(|err| WhifError::std_io(format!("{:?}", err)))
            .map_err(detailed_whif_error!("Failed to invoke MiniZinc solver"))?;

        let mut pipe = command
            .stdin
            .take()
            .ok_or_else(|| WhifError::std_io("Child process error"))
            .map_err(detailed_whif_error!("Failed to get stdin from MiniZinc solver"))?;

        let mut capture = if let Some(ref path) = self.path_to_capture {
            Some(File::create(path)?)
        } else {
            None
        };

        let generator = std::thread::spawn(move || {
            if this.verbosity > 2 {
                println!("\n%% Start of MiniZinc code.");
            }

            for source in 0..problem.substitutions.len() {
                let (lower_limit, upper_limit) = problem.domains[source];
                let line = if let Some(sub) = problem.substitutions[source] {
                    // FIXME multiplier
                    if sub.offset.is_zero() {
                        format!(
                            "var {}..{}: sol_{} = sol_{};",
                            lower_limit, upper_limit, source, sub.target
                        )
                    } else {
                        format!(
                            "var {}..{}: sol_{} = sol_{} + {};",
                            lower_limit, upper_limit, source, sub.target, sub.offset
                        )
                    }
                } else {
                    format!("var {}..{}: sol_{};", lower_limit, upper_limit, source)
                };

                Self::pipeout(&mut pipe, capture.as_mut(), line, this.verbosity);
            }

            let dim = problem.constraints.len();

            // traverse lower triangle => row > col
            for row in 1..dim {
                for col in 0..row {
                    let line = if let Some(cst) = problem.constraints[row][col] {
                        use Relation::*;

                        match cst.rel {
                            Contradiction => {
                                if cst.row == cst.col {
                                    format!(
                                        "%B sol_{} has empty domain (derived from {}:{})",
                                        cst.row, row, col
                                    )
                                } else {
                                    format!(
                                        "%C sol_{} - sol_{} is contradictory (derived from {}:{})",
                                        cst.row, cst.col, row, col
                                    )
                                }
                            }
                            Unconstrained => {
                                if cst.row == cst.col {
                                    format!(
                                        "%T sol_{} has unconstrained domain (derived from {}:{})",
                                        cst.row, row, col
                                    )
                                } else {
                                    format!(
                                        "%U sol_{} - sol_{} is unconstrained (derived from {}:{})",
                                        cst.row, cst.col, row, col
                                    )
                                }
                            }
                            _ => format!("constraint {};", cst),
                        }
                    } else if let Some(sub) = problem.substitutions[row] {
                        // FIXME multiplier
                        if sub.offset.is_zero() {
                            format!("%P sol_{} == sol_{} has been propagated", row, sub.target)
                        } else {
                            format!(
                                "%O sol_{} == sol_{} + {} has been propagated",
                                row, sub.target, sub.offset
                            )
                        }
                    } else if problem.mergeouts.contains(&(row, col)) {
                        format!("%M sol_{} - sol_{} is merged out", row, col)
                    } else {
                        format!("%U sol_{} - sol_{} is unconstrained", row, col)
                    };

                    Self::pipeout(&mut pipe, capture.as_mut(), line, this.verbosity);
                }
            }

            let mut line = "solve satisfy;\noutput [".to_string();

            for i in 0..dim - 1 {
                line.push_str(&format!("show(sol_{}), \" \", ", i));
            }

            line.push_str(&format!("show(sol_{})];", dim - 1));

            Self::pipeout(&mut pipe, capture.as_mut(), line, this.verbosity);

            if this.verbosity > 2 {
                println!("%% End of MiniZinc code.\n");
            }
        });

        let child = command
            .wait_with_output()
            .map_err(|err| WhifError::std_io(format!("{:?}", err)))
            .map_err(detailed_whif_error!("Error waiting for output piped from MiniZinc solver"))?;

        generator.join().map_err(|err| WhifError::std_io(format!("{:?}", err)))?;

        let unparsed_output = String::from_utf8(child.stdout)
            .map_err(|err| WhifError::std_io(format!("{:?}", err)))?;

        let mut result = Vec::new();
        let output = unparsed_output.trim_start();

        if output.starts_with('=') {
            eprintln!("  solving failed...");
        } else {
            for line in output.lines() {
                let mut solution = Vec::new();

                for word in line.split_whitespace() {
                    let elt: T = word
                        .parse()
                        .map_err(|err| WhifError::std_io(format!("{:?}", err)))
                        .map_err(detailed_whif_error!(
                            "Error parsing piped output of MiniZinc solver"
                        ))?;

                    solution.push(elt);
                }

                if !solution.is_empty() {
                    result.push(solution);
                }
            }
        }

        Ok((result, unparsed_output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_update_domains_unary_leq() {
        let mut cst: Constraint<i32> =
            Constraint { row: 0, col: 0, mur: 3, muc: 1, rel: Relation::Leq(-6) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (Some((-10, -3)), Some((-10, -3))));
        assert_eq!(cst.rel, Relation::Unconstrained);
    }

    #[test]
    fn test_update_domains_unary_or_keep() {
        let mut cst: Constraint<i32> =
            Constraint { row: 0, col: 0, mur: 3, muc: 1, rel: Relation::Or(-3, -6) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (None, None));
        assert_eq!(cst.rel, Relation::Or(-1, -3));
    }

    #[test]
    fn test_update_domains_unary_or_shrink() {
        let mut cst: Constraint<i32> =
            Constraint { row: 0, col: 0, mur: 3, muc: 1, rel: Relation::Or(-5, -21) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (Some((-2, 10)), Some((-2, 10))));
        assert_eq!(cst.rel, Relation::Unconstrained);
    }

    #[test]
    fn test_update_domains_equality_two_passes() {
        let mut cst: Constraint<i32> =
            Constraint { row: 1, col: 0, mur: 1, muc: 3, rel: Relation::Equality(-6) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (Some((-9, 9)), Some((-1, 5))));
        assert_eq!(cst.rel, Relation::Equality(-6));
    }

    #[test]
    fn test_update_domains_equality_unconstrained() {
        let mut cst: Constraint<i32> =
            Constraint { row: 1, col: 0, mur: 1, muc: 1, rel: Relation::Equality(20) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (Some((10, 10)), Some((-10, -10))));
        assert_eq!(cst.rel, Relation::Unconstrained);
    }

    #[test]
    fn test_update_domains_equality_contradiction() {
        let mut cst: Constraint<i32> =
            Constraint { row: 1, col: 0, mur: 1, muc: 1, rel: Relation::Equality(123) };
        let domains = cst.update_domains((-10, 10), (-10, 10));
        assert_eq!(domains, (None, None));
        assert_eq!(cst.rel, Relation::Contradiction);
    }
}

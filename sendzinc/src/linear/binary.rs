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
    Contradiction,
    Unconstrained,
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub struct Constraint<T: Scalar> {
    row: usize,
    col: usize,
    mur: T,
    muc: T,
    rel: Relation<T>,
}

impl<T: Scalar> Constraint<T> {
    fn simplify(&mut self) {
        let gcd = self.mur.gcd(&self.muc);

        if !gcd.is_one() {
            use Relation::*;

            self.mur /= gcd;
            self.muc /= gcd;

            match self.rel {
                Equality(hiv) => {
                    if hiv.is_multiple_of(&gcd) {
                        self.rel = Equality(hiv / gcd);
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
    pub fn new(row: usize, col: usize, mur: T, muc: T, rel: Relation<T>) -> Self {
        let mut cst = Constraint { row, col, mur, muc, rel };

        cst.simplify();

        cst
    }

    #[inline]
    pub fn new_delta(row: usize, col: usize, rel: Relation<T>) -> Self {
        Constraint { row, col, mur: T::one(), muc: T::one(), rel }
    }

    #[inline]
    pub fn is_delta(&self) -> bool {
        self.mur == self.muc // assuming simplification
    }

    fn apply_substitutions(
        &mut self,
        left_sub: Option<Substitution<T>>,
        right_sub: Option<Substitution<T>>,
    ) {
        use Relation::*;

        if !self.is_delta() {
            // FIXME
            return
        }

        let left_sub = left_sub.unwrap_or(Substitution::new(self.row));
        let right_sub = right_sub.unwrap_or(Substitution::new(self.col));
        let offset = left_sub.offset - right_sub.offset;

        // FIXME multiplier

        match self.rel {
            Leq(hiv) => {
                // sol_row - sol_col == left_mul * sol_row' + left_offset - right_mul * sol_col' - right_offset <= hiv
                if left_sub.target == right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = if offset <= hiv { Unconstrained } else { Contradiction };
                } else if left_sub.target > right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = Leq(hiv - offset);
                } else {
                    self.row = right_sub.target;
                    self.col = left_sub.target;
                    self.rel = Geq(offset - hiv);
                }
            }
            Geq(lov) => {
                // sol_row - sol_col == left_mul * sol_row' + left_offset - right_mul * sol_col' - right_offset >= lov
                if left_sub.target == right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = if offset >= lov { Unconstrained } else { Contradiction };
                } else if left_sub.target > right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = Geq(lov - offset);
                } else {
                    self.row = right_sub.target;
                    self.col = left_sub.target;
                    self.rel = Leq(offset - lov);
                }
            }
            Or(lov, hiv) => {
                if left_sub.target == right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel =
                        if offset >= lov || offset <= hiv { Unconstrained } else { Contradiction };
                } else if left_sub.target > right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = Or(lov - offset, hiv - offset);
                } else {
                    self.row = right_sub.target;
                    self.col = left_sub.target;
                    self.rel = Or(offset - hiv, offset - lov);
                }
            }
            And(lov, hiv) => {
                if left_sub.target == right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel =
                        if offset >= lov && offset <= hiv { Unconstrained } else { Contradiction };
                } else if left_sub.target > right_sub.target {
                    self.row = left_sub.target;
                    self.col = right_sub.target;
                    self.rel = And(lov - offset, hiv - offset);
                } else {
                    self.row = right_sub.target;
                    self.col = left_sub.target;
                    self.rel = And(offset - hiv, offset - lov);
                }
            }
            _ => {
                // FIXME error
            }
        }
    }
}

impl<T: Scalar> std::fmt::Display for Constraint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Relation::*;

        if self.is_delta() {
            let Constraint { row, col, rel, .. } = *self;

            match rel {
                Equality(hiv) => {
                    if hiv.is_zero() {
                        write!(f, "sol_{} == sol_{}", row, col)
                    } else {
                        write!(f, "sol_{} == sol_{} + {}", row, col, hiv)
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
                Equality(hiv) => {
                    if hiv.is_zero() {
                        fmt_sol(f, mur, row)?;
                        write!(f, " == ")?;
                        fmt_sol(f, muc, col)
                    } else {
                        fmt_sol(f, mur, row)?;
                        write!(f, " == ")?;
                        fmt_sol(f, muc, col)?;
                        write!(f, " + {}", hiv)
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

#[derive(Clone, Debug)]
pub struct Problem<T: Scalar> {
    constraints:   Vec<Vec<Option<Constraint<T>>>>,
    substitutions: Vec<Option<Substitution<T>>>,
    mergeouts:     HashSet<(usize, usize)>,
    verbosity:     u32,
}

impl<T: Scalar> Problem<T> {
    pub fn add_constraint(&mut self, row: usize, col: usize, mut cst: Constraint<T>) {
        assert!(row < self.constraints.len());

        cst.simplify();

        match cst.rel {
            Relation::Equality(mut offset) => {
                if cst.is_delta() {
                    let Constraint { row: source, col: mut target, .. } = cst;

                    // FIXME multiplier

                    while let Some(next_sub) = self.substitutions[target] {
                        target = next_sub.target;
                        offset += next_sub.offset;
                    }

                    self.constraints[row][col] = None;
                    self.substitutions[source] =
                        Some(Substitution { target, multiplier: T::one(), offset });
                } else {
                    // FIXME non-delta substitution
                    self.constraints[row][col] = Some(cst);
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

    pub fn preprocess(&mut self) {
        self.propagate_substitutions();
        self.merge_constraints();
        self.sweep_constraints();
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

        self.remove_unconstrained();
    }
}

#[derive(Clone, Debug)]
pub struct Solver<T: Scalar> {
    upper_limit:       T,
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
            max_solutions:     1,
            path_to_minizinc:  None,
            path_to_flatfile:  None,
            path_to_pathsfile: None,
            path_to_capture:   None,
            verbosity:         0,
        }
    }

    pub fn with_upper_limit(mut self, upper_limit: T) -> Self {
        self.set_upper_limit(upper_limit);
        self
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

    #[inline]
    pub fn set_upper_limit(&mut self, upper_limit: T) {
        self.upper_limit = upper_limit;
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

    pub fn get_problem(&self, dim: usize) -> Problem<T> {
        let constraints = (0..dim).map(|row| [None].repeat(row)).collect();
        let substitutions = [None].repeat(dim);
        let mergeouts = HashSet::new();
        let verbosity = self.verbosity;

        Problem { constraints, substitutions, mergeouts, verbosity }
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
                let line = if let Some(sub) = problem.substitutions[source] {
                    // FIXME multiplier
                    if sub.offset.is_zero() {
                        format!(
                            "var -{}..{}: sol_{} = sol_{};",
                            this.upper_limit, this.upper_limit, source, sub.target
                        )
                    } else {
                        format!(
                            "var -{}..{}: sol_{} = sol_{} + {};",
                            this.upper_limit, this.upper_limit, source, sub.target, sub.offset
                        )
                    }
                } else {
                    format!("var -{}..{}: sol_{};", this.upper_limit, this.upper_limit, source)
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

#![feature(io_error_more)]

use std::path::PathBuf;
use nalgebra as na;
use whif::io;
use whif_sendzinc::blint;

mod ad_hoc;

#[derive(Debug)]
struct App {
    user_jump:     Vec<i32>,
    input_path:    PathBuf,
    jump_path:     Option<PathBuf>,
    flatfile_path: Option<PathBuf>,
    capture_path:  Option<PathBuf>,
    upper_limit:   Option<i32>,
    max_solutions: Option<u32>,
    verbosity:     u32,
}

impl App {
    const DEFAULT_DATA_DIR: &'static str = "data";
    const DEFAULT_INPUT_FILENAME: &'static str = "small-test.mat";

    fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let mut user_jump = Vec::new();
        let mut data_path = None;
        let mut input_filename = None;
        let mut jump_filename = None;
        let mut flat_filename = None;
        let mut capture_filename = None;
        let mut upper_limit = None;
        let mut max_solutions = None;
        let mut verbosity = 0;

        for (prev_arg, next_arg) in std::env::args().zip(std::env::args().skip(1)) {
            if user_jump.is_empty() {
                match next_arg.as_str() {
                    "-v" => verbosity += 1,
                    "-vv" => verbosity += 2,
                    "-vvv" => verbosity += 3,
                    "-vvvv" => verbosity += 4,
                    "-vvvvv" => verbosity += 5,
                    "-i" | "-j" | "-f" | "-c" | "-d" | "--up" | "--max" => {}
                    arg => match prev_arg.as_str() {
                        "-i" => input_filename = Some(PathBuf::from(arg)),
                        "-j" => jump_filename = Some(PathBuf::from(arg)),
                        "-f" => flat_filename = Some(PathBuf::from(arg)),
                        "-c" => capture_filename = Some(PathBuf::from(arg)),
                        "-d" => data_path = Some(PathBuf::from(arg)),
                        "--up" => {
                            upper_limit = Some(arg.parse().expect(&format!(
                                "ERROR: Invalid value of `upper_limit`, \"{}\".",
                                arg
                            )))
                        }
                        "--max" => {
                            max_solutions = Some(arg.parse().expect(&format!(
                                "ERROR: Invalid value of `max_solutions`, \"{}\".",
                                arg
                            )))
                        }
                        _ => {
                            let elt: i32 = if arg.starts_with('-') {
                                arg.parse()
                                    .expect(&format!("ERROR: Invalid CLI option, \"{}\".", arg))
                            } else {
                                arg.parse().expect(&format!(
                                    "ERROR: Invalid first element of jump vector, \"{}\".",
                                    arg,
                                ))
                            };
                            user_jump.push(elt);
                        }
                    },
                }
            } else {
                let elt: i32 = next_arg
                    .parse()
                    .expect(&format!("ERROR: Invalid element of jump vector, \"{}\".", next_arg));
                user_jump.push(elt);
            }
        }

        let data_path = data_path.unwrap_or_else(|| PathBuf::from(Self::DEFAULT_DATA_DIR));

        if !std::fs::metadata(&data_path)?.is_dir() {
            return Err(std::io::Error::from(std::io::ErrorKind::NotADirectory).into())
        }

        let mut out_path = data_path.join("out");

        if !std::fs::metadata(&out_path).map(|metadata| metadata.is_dir()).unwrap_or(true) {
            out_path.pop();
        }

        let input_path = data_path.join(input_filename.unwrap_or_else(|| {
            if verbosity > 0 {
                eprintln!(
                    "[WARN] Unspecified input filename; using \"{}\".",
                    Self::DEFAULT_INPUT_FILENAME
                );
            }
            PathBuf::from(Self::DEFAULT_INPUT_FILENAME)
        }));

        let jump_path = jump_filename.map(|path| data_path.join(path));
        let flatfile_path = flat_filename.map(|path| out_path.join(path));
        let capture_path = capture_filename.map(|path| out_path.join(path));

        if verbosity > 1 {
            if let Some(ref jump_path) = jump_path {
                eprintln!("Input path: {:?}, jump path: {:?}.", input_path, jump_path);
            } else {
                eprintln!("Input path: {:?}.", input_path);
            }
            if let Some(ref flatfile_path) = flatfile_path {
                eprintln!("Flatfile path: {:?}.", flatfile_path);
            }
            if let Some(ref capture_path) = capture_path {
                eprintln!("Capture path: {:?}.", capture_path);
            }
        }

        Ok(App {
            user_jump,
            input_path,
            jump_path,
            flatfile_path,
            capture_path,
            upper_limit,
            max_solutions,
            verbosity,
        })
    }

    #[inline]
    fn start(&self, message: &str) -> Option<std::time::Instant> {
        if self.verbosity >= 1 {
            eprint!("{}", message);
            Some(std::time::Instant::now())
        } else {
            None
        }
    }
}

#[inline]
fn done(start_time: Option<std::time::Instant>) {
    if let Some(elapsed) = start_time.map(|t| t.elapsed().as_micros()) {
        eprintln!(" Done ({} us).", elapsed);
    }
}

pub fn create_problem(
    solver: &blint::Solver<i32>,
    source_matrix: na::DMatrix<i32>,
) -> Result<blint::Problem<i32>, Box<dyn std::error::Error>> {
    let dim = source_matrix.nrows();
    let upper_limit = solver.get_upper_limit();
    let infinity = upper_limit + upper_limit; // target(r,c) |-> source(r,c) + sol(r) - sol(c)
    let mut problem = solver.get_problem(dim);

    // traverse lower triangle => row > col
    for row in 1..dim {
        for col in 0..row {
            // delta = sol[row] - sol[col]
            // optimal solution: -lov + delta >= 0 and hiv - delta >= 0
            // hence: lov <= delta <= hiv
            // if lov > hiv, then suboptimal solution:
            // not (-lov + delta < 0 and hiv - delta < 0)
            // hence: delta >= lov or delta <= hiv

            let lov = -source_matrix[(row, col)];
            let hiv = source_matrix[(col, row)];
            let rel = blint::Relation::from_interval(lov, hiv, infinity);

            problem.add_constraint(row, col, 1, 1, rel)?;
        }
    }

    Ok(problem)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let app = App::new()?;
    let (vec, dim) = io::load_square_matrix(&app.input_path);
    let mut ad_hoc_solver = ad_hoc::Solver::from_vec_and_dim(vec, dim);

    if app.verbosity >= 3 {
        eprint!("Source{}", ad_hoc_solver.current_source_matrix());
    } else {
        eprintln!("Dimension {}", dim);
    }

    if let Some(ref jump_path) = app.jump_path {
        let vec = io::load_vector(jump_path);

        ad_hoc_solver.push_jump((vec.as_slice(), dim));
    } else if !app.user_jump.is_empty() {
        ad_hoc_solver.push_jump((app.user_jump.as_slice(), dim));
    } else {
        let mut solver = blint::Solver::<i32>::new().with_verbosity(app.verbosity);

        if let Some(upper_limit) = app.upper_limit {
            solver.set_upper_limit(upper_limit);
        }
        if let Some(max_solutions) = app.max_solutions {
            solver.set_max_solutions(max_solutions);
        }
        if let Some(ref flatfile_path) = app.flatfile_path {
            solver.set_flatfile(flatfile_path)?;
        }
        if let Some(ref capture_path) = app.capture_path {
            solver.set_capture(capture_path)?;
        }

        let start_time = app.start("Creating the problem...");
        let source_matrix = ad_hoc_solver.get_origin_matrix().clone();
        let problem = create_problem(&mut solver, source_matrix)?;
        done(start_time);

        let start_time = app.start("Solving the problem...");
        let (jumps, unparsed_output) = solver.solve(problem)?;
        done(start_time);

        if app.verbosity > 0 {
            eprintln!("Got: {}", unparsed_output);
        }

        for jump in jumps {
            ad_hoc_solver.rewind();
            ad_hoc_solver.push_jump((jump.as_slice(), dim));
        }
    }

    let mut best_score = std::i32::MIN;

    for solution in ad_hoc_solver.get_all_solutions() {
        eprint!("Jump vector^T{}", solution.get_jump_vector().transpose());

        let score = solution.get_score();

        if best_score < score {
            best_score = score;
        }

        if app.verbosity >= 4 {
            if app.verbosity >= 5 {
                eprint!("Jump matrix{}", ad_hoc_solver.current_solution_matrix());
            }
            eprintln!("Target (score {}){}", score, ad_hoc_solver.current_target_matrix());
        } else {
            eprintln!("Score {}", score);
        }
    }

    if ad_hoc_solver.get_num_solutions() > 1 {
        eprintln!("\nBest score {}", best_score);
    }

    Ok(())
}

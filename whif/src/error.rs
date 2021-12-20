pub trait DetailedWhifError {
    fn with_details<S: AsRef<str>>(self, details: S) -> WhifError;
}

#[macro_export]
macro_rules! detailed_whif_error {
    ($($arg:tt)*) => {{
        |err| {
            let message = format!($($arg)*);
            error!("{}", message);
            err.with_details(message)
        }
    }}
}

#[derive(Debug)]
enum InnerError {
    IO(std::io::Error),
    UndeclaredVariable(usize),
    UndeclaredConstraint(Vec<usize>),
    Domain(Option<usize>),
}

macro_rules! impl_inner_error {
    ($error:ty, $variant:ident) => {
        impl DetailedWhifError for $error {
            fn with_details<S: AsRef<str>>(self, details: S) -> WhifError {
                InnerError::from(self).with_details(details)
            }
        }

        impl From<$error> for InnerError {
            #[inline]
            fn from(err: $error) -> Self {
                InnerError::$variant(err)
            }
        }

        impl From<$error> for WhifError {
            #[inline]
            fn from(err: $error) -> Self {
                WhifError { inner: err.into(), details: None }
            }
        }
    };
}

impl_inner_error!(std::io::Error, IO);

impl DetailedWhifError for InnerError {
    #[inline]
    fn with_details<S: AsRef<str>>(self, details: S) -> WhifError {
        WhifError::from(self).with_details(details)
    }
}

impl std::fmt::Display for InnerError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use InnerError::*;

        match self {
            IO(err) => write!(f, "IO error {:?}", err),
            UndeclaredVariable(var) => write!(f, "Undeclared variable sol_{}", var),
            UndeclaredConstraint(vars) => if let Some((head, tail)) = vars.split_first() {
                if tail.is_empty() {
                    write!(f, "Undeclared unary constraint for sol_{}", head)
                } else {
                    write!(f, "Undeclared constraint for variables: sol_{}", head)?;
                    for var in tail {
                        write!(f, ", sol_{}", var)?;
                    }
                    Ok(())
                }
            } else {
                write!(f, "Unexpected nullary constraint")
            }
            Domain(var) => {
                if let Some(var) = var {
                    write!(f, "Domain error for sol_{}", var)
                } else {
                    write!(f, "Domain error")
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct WhifError {
    inner:   InnerError,
    details: Option<String>,
}

impl WhifError {
    pub fn std_io<E>(err: E) -> Self
    where
        E: Into<Box<dyn std::error::Error + Send + Sync>>,
    {
        std::io::Error::new(std::io::ErrorKind::Other, err).into()
    }

    pub fn undeclared_variable(var: usize) -> Self {
        WhifError { inner: InnerError::UndeclaredVariable(var), details: None }
    }

    pub fn undeclared_constraint(vars: Vec<usize>) -> Self {
        WhifError { inner: InnerError::UndeclaredConstraint(vars), details: None }
    }

    pub fn domain(var: Option<usize>) -> Self {
        WhifError { inner: InnerError::Domain(var), details: None }
    }
}

impl DetailedWhifError for WhifError {
    fn with_details<S: AsRef<str>>(mut self, details: S) -> WhifError {
        self.details = Some(details.as_ref().to_string());
        self
    }
}

impl From<InnerError> for WhifError {
    #[inline]
    fn from(inner: InnerError) -> Self {
        WhifError { inner, details: None }
    }
}

impl std::fmt::Display for WhifError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(ref details) = self.details {
            write!(f, "{:?}: {}", self.inner, details)
        } else {
            self.inner.fmt(f)
        }
    }
}

impl std::error::Error for WhifError {}

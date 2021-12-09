pub trait DetailedWhifError {
    fn with_details(self, details: String) -> WhifError;
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
}

macro_rules! impl_inner_error {
    ($error:ty, $variant:ident) => {
        impl DetailedWhifError for $error {
            fn with_details(self, details: String) -> WhifError {
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
    fn with_details(self, details: String) -> WhifError {
        WhifError::from(self).with_details(details)
    }
}

impl std::fmt::Display for InnerError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use InnerError::*;

        match self {
            IO(err) => write!(f, "IO error {:?}", err),
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
}

impl DetailedWhifError for WhifError {
    fn with_details(mut self, details: String) -> WhifError {
        self.details = Some(details);
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

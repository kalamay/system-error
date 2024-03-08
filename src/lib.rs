//! A library for cross platform system errors.
//!
//! This library captures the behavior and messaging for `errno` on unix platforms,
//! `GetLastError()` on Windows, and `kern_return_t` on macOS and iOS. Additionally,
//! these [`Error`] values can be converted into `std::io::Error` values.
//!
//! # Examples
//!
//! On Linux:
//!
//! ```
//! # if cfg!(target_os = "linux") {
//! use system_error::Error;
//! use std::io::ErrorKind;
//!
//! let os_error = Error::from_raw_os_error(1);
//! assert_eq!(os_error.kind(), ErrorKind::PermissionDenied);
//! assert_eq!(
//!     format!("{}", os_error),
//!     "Operation not permitted (os error 1)"
//! );
//! assert_eq!(
//!     format!("{:?}", os_error),
//!     "Error { kind: PermissionDenied, message: \"Operation not permitted (os error 1)\" }"
//! );
//!
//! let kern_error = Error::from_raw_kernel_error(8);
//! assert_eq!(kern_error.kind(), ErrorKind::Other);
//! assert_eq!(
//!     format!("{}", kern_error),
//!     "Unknown error (kernel error 8)"
//! );
//! assert_eq!(
//!     format!("{:?}", kern_error),
//!     "Error { kind: Other, message: \"Unknown error (kernel error 8)\" }"
//! );
//! # }
//! ```
//!
//! On macOS:
//!
//! ```
//! # if cfg!(target_os = "macos") {
//! use system_error::Error;
//! use std::io::ErrorKind;
//!
//! let os_error = Error::from_raw_os_error(1);
//! assert_eq!(os_error.kind(), ErrorKind::PermissionDenied);
//! assert_eq!(
//!     format!("{}", os_error),
//!     "Operation not permitted (os error 1)"
//! );
//! assert_eq!(
//!     format!("{:?}", os_error),
//!     "Error { kind: PermissionDenied, message: \"Operation not permitted (os error 1)\" }"
//! );
//!
//! let kern_error = Error::from_raw_kernel_error(8);
//! assert_eq!(kern_error.kind(), ErrorKind::PermissionDenied);
//! assert_eq!(
//!     format!("{}", kern_error),
//!     "(os/kern) no access (kernel error 8)"
//! );
//! assert_eq!(
//!     format!("{:?}", kern_error),
//!     "Error { kind: PermissionDenied, message: \"(os/kern) no access (kernel error 8)\" }"
//! );
//! # }
//! ```
//!
//! On Windows:
//!
//! ```
//! # if cfg!(windows) {
//! use system_error::Error;
//! use std::io::ErrorKind;
//!
//! let os_error = Error::from_raw_os_error(5);
//! assert_eq!(os_error.kind(), ErrorKind::PermissionDenied);
//! assert_eq!(
//!     format!("{}", os_error),
//!     "Access is denied. (os error 5)"
//! );
//! assert_eq!(
//!     format!("{:?}", os_error),
//!     "Error { kind: PermissionDenied, message: \"Access is denied. (os error 5)\" }"
//! );
//!
//! let kern_error = Error::from_raw_kernel_error(8);
//! assert_eq!(kern_error.kind(), ErrorKind::Other);
//! assert_eq!(
//!     format!("{}", kern_error),
//!     "Unknown error (kernel error 8)"
//! );
//! assert_eq!(
//!     format!("{:?}", kern_error),
//!     "Error { kind: Other, message: \"Unknown error (kernel error 8)\" }"
//! );
//! # }
//! ```

use std::convert::TryFrom;
use std::os::raw::c_int;
use std::str::Utf8Error;
use std::{error, fmt, io};

/// An error type for cross platform system-level errors.
///
/// This type captures the behavior and error message for `errno` on unix platforms,
/// `GetLastError()` on Windows, and `kern_return_t` on macOS and iOS.
pub struct Error(Type);

/// A type for storing operating system error codes.
///
/// This is used for libc or Windows errors (i.e. `errno` or `GetLastError`).
pub type OsCode = i32;

/// A type for storing kernel error codes.
///
/// This is *not* used for libc or Windows errors (i.e. `errno` or
/// `GetLastError`). On macOS and iOS, some platform invocations use a different
/// error mechanism (i.e. `kern_return_t`), and this is used to hold that value.
///
/// On other platforms this isn't generally used. However, to maintain cross-
/// platform use of the error, it is implemented across all platforms.
pub type KernelCode = c_int;

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct KernelError(KernelCode);

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
enum Type {
    Os(OsCode),
    Kernel(KernelCode),
}

impl Error {
    /// Returns an error representing the last OS error which occurred.
    ///
    /// This function reads the value of `errno` for the target platform (e.g.
    /// `GetLastError` on Windows) and will return a corresponding instance of
    /// `Error` for the error code.
    ///
    /// # Examples
    ///
    /// ```
    /// use system_error::Error;
    ///
    /// println!("last OS error: {:?}", Error::last_os_error());
    /// ```
    pub fn last_os_error() -> Self {
        Self::from_raw_os_error(io::Error::last_os_error().raw_os_error().unwrap())
    }

    /// Creates a new instance of an `Error` from a particular OS error code.
    ///
    /// # Examples
    ///
    /// On Linux:
    ///
    /// ```
    /// # if cfg!(target_os = "linux") {
    /// use system_error::Error;
    /// use std::io;
    ///
    /// let error = Error::from_raw_os_error(22);
    /// assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    /// # }
    /// ```
    ///
    /// On Windows:
    ///
    /// ```
    /// # if cfg!(windows) {
    /// use system_error::Error;
    /// use std::io;
    ///
    /// let error = Error::from_raw_os_error(10022);
    /// assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    /// # }
    /// ```
    pub fn from_raw_os_error(code: OsCode) -> Self {
        Self(Type::Os(code))
    }

    /// Creates a new instance of an `Error` from a particular kernel error code.
    ///
    /// # Examples
    ///
    /// On macOS:
    ///
    /// ```
    /// # if cfg!(target_os = "macos") {
    /// use system_error::Error;
    /// use std::io;
    ///
    /// let error = Error::from_raw_kernel_error(4);
    /// assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    /// # }
    /// ```
    ///
    /// On Linux:
    ///
    /// ```
    /// # if cfg!(target_os = "linux") {
    /// use system_error::Error;
    /// use std::io;
    ///
    /// let error = Error::from_raw_kernel_error(4);
    /// assert_eq!(error.kind(), io::ErrorKind::Other);
    /// # }
    /// ```
    pub fn from_raw_kernel_error(code: KernelCode) -> Self {
        Self(Type::Kernel(code))
    }

    /// Returns the corresponding `ErrorKind` for this error.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(not(target_os = "windows")) {
    /// use system_error::Error;
    /// use std::io;
    ///
    /// assert_eq!(Error::from_raw_os_error(1).kind(), io::ErrorKind::PermissionDenied);
    /// # }
    /// ```
    pub fn kind(&self) -> io::ErrorKind {
        match self.0 {
            Type::Os(code) => io::Error::from_raw_os_error(code).kind(),
            Type::Kernel(code) => KernelError::new(code).kind(),
        }
    }

    /// Returns the OS error that this error represents (if any).
    ///
    /// If this `Error` was constructed via `last_os_error` or
    /// `from_raw_os_error`, then this function will return `Some`, otherwise
    /// it will return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use system_error::Error;
    ///
    /// fn print_os_error(err: &Error) {
    ///     if let Some(raw_os_err) = err.raw_os_error() {
    ///         println!("raw OS error: {:?}", raw_os_err);
    ///     } else {
    ///         println!("Not an OS error");
    ///     }
    /// }
    ///
    /// let os_err = Error::last_os_error();
    /// let kern_err = Error::from_raw_kernel_error(8);
    ///
    /// // Will print "raw OS error: ...".
    /// print_os_error(&os_err);
    /// // Will print "Not an OS error".
    /// print_os_error(&kern_err);
    ///
    /// assert!(os_err.raw_os_error().is_some());
    /// assert_eq!(kern_err.raw_os_error(), None);
    /// ```
    pub fn raw_os_error(&self) -> Option<i32> {
        match self.0 {
            Type::Os(code) => Some(code),
            _ => None,
        }
    }

    /// Returns the kernel error that this error represents (if any).
    ///
    /// If this `Error` was constructed via `from_raw_kernel_error` then this
    /// function will return `Some`, otherwise it will return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use system_error::Error;
    ///
    /// fn print_kernel_error(err: &Error) {
    ///     if let Some(raw_kernel_err) = err.raw_kernel_error() {
    ///         println!("raw kernel error: {:?}", raw_kernel_err);
    ///     } else {
    ///         println!("Not an kernel error");
    ///     }
    /// }
    ///
    /// let kern_err = Error::from_raw_kernel_error(8);
    /// let os_err = Error::last_os_error();
    ///
    /// // Will print "raw kernel error: 8".
    /// print_kernel_error(&kern_err);
    /// // Will print "Not an kernel error".
    /// print_kernel_error(&os_err);
    ///
    /// assert_eq!(kern_err.raw_kernel_error(), Some(8));
    /// assert_eq!(os_err.raw_kernel_error(), None);
    /// ```
    pub fn raw_kernel_error(&self) -> Option<i32> {
        match self.0 {
            Type::Kernel(code) => Some(code),
            _ => None,
        }
    }
}

impl error::Error for Error {}

impl fmt::Debug for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let (kind, message) = match self.0 {
            Type::Os(code) => {
                let err = io::Error::from_raw_os_error(code);
                (err.kind(), format!("{}", &err))
            }
            Type::Kernel(code) => {
                let err = KernelError::new(code);
                (err.kind(), format!("{}", &err))
            }
        };
        fmt.debug_struct("Error")
            .field("kind", &kind)
            .field("message", &message)
            .finish()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Type::Os(code) => fmt::Display::fmt(&io::Error::from_raw_os_error(code), fmt),
            Type::Kernel(code) => fmt::Display::fmt(&KernelError::new(code), fmt),
        }
    }
}

impl Into<io::Error> for Error {
    fn into(self) -> io::Error {
        match self.0 {
            Type::Os(code) => io::Error::from_raw_os_error(code),
            Type::Kernel(code) => {
                let err = KernelError::new(code);
                io::Error::new(err.kind(), err)
            }
        }
    }
}

impl TryFrom<io::Error> for Error {
    type Error = io::Error;

    fn try_from(io: io::Error) -> Result<Self, io::Error> {
        match io.raw_os_error() {
            Some(code) => Ok(Self(Type::Os(code))),
            None => Err(io),
        }
    }
}

impl KernelError {
    pub fn new(code: KernelCode) -> Self {
        Self(code)
    }
}

#[cfg(not(any(target_os = "macos", target_os = "ios")))]
impl KernelError {
    /// Converts the `KernelCode` into the most appropriate message `str`.
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        Ok("Unknown error")
    }

    /// Converts the `KernelCode` into the most appropriate `std::io::ErrorKind`.
    pub fn kind(&self) -> io::ErrorKind {
        io::ErrorKind::Other
    }
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
impl KernelError {
    /// The operation succeeded.
    pub const KERN_SUCCESS: KernelCode = 0;
    /// Specified address is not currently valid.
    pub const KERN_INVALID_ADDRESS: KernelCode = 1;
    /// Specified memory is valid, but does not permit the required
    /// forms of access.
    pub const KERN_PROTECTION_FAILURE: KernelCode = 2;
    /// The address range specified is already in use, or no address
    /// range of the size specified could be found.
    pub const KERN_NO_SPACE: KernelCode = 3;
    /// The function requested was not applicable to this type of argument,
    /// or an argument is invalid
    pub const KERN_INVALID_ARGUMENT: KernelCode = 4;
    /// The function could not be performed. A catch-all.
    pub const KERN_FAILURE: KernelCode = 5;
    /// A system resource could not be allocated to fulfill this request.
    /// This failure may not be permanent.
    pub const KERN_RESOURCE_SHORTAGE: KernelCode = 6;
    /// The task in question does not hold receive rights for the port argument.
    pub const KERN_NOT_RECEIVER: KernelCode = 7;
    /// Bogus access restriction.
    pub const KERN_NO_ACCESS: KernelCode = 8;
    /// During a page fault, the target address refers to a memory object
    /// that has been destroyed. This failure is permanent.
    pub const KERN_MEMORY_FAILURE: KernelCode = 9;
    /// During a page fault, the memory object indicated that the data could
    /// not be returned. This failure may be temporary; future attempts to
    /// access this same data may succeed, as defined by the memory object.
    pub const KERN_MEMORY_ERROR: KernelCode = 10;
    /// The receive right is already a member of the portset.
    pub const KERN_ALREADY_IN_SET: KernelCode = 11;
    /// The receive right is not a member of a port set.
    pub const KERN_NOT_IN_SET: KernelCode = 12;
    /// The name already denotes a right in the task.
    pub const KERN_NAME_EXISTS: KernelCode = 13;
    /// The operation was aborted. Ipc code will catch this and reflect it as
    /// a message error.
    pub const KERN_ABORTED: KernelCode = 14;
    /// The name doesn't denote a right in the task.
    pub const KERN_INVALID_NAME: KernelCode = 15;
    /// Target task isn't an active task.
    pub const KERN_INVALID_TASK: KernelCode = 16;
    /// The name denotes a right, but not an appropriate right.
    pub const KERN_INVALID_RIGHT: KernelCode = 17;
    /// A blatant range error.
    pub const KERN_INVALID_VALUE: KernelCode = 18;
    /// Operation would overflow limit on user-references.
    pub const KERN_UREFS_OVERFLOW: KernelCode = 19;
    /// The supplied (port) capability is improper.
    pub const KERN_INVALID_CAPABILITY: KernelCode = 20;
    /// The task already has send or receive rights for the port under another name.
    pub const KERN_RIGHT_EXISTS: KernelCode = 21;
    /// Target host isn't actually a host.
    pub const KERN_INVALID_HOST: KernelCode = 22;
    /// An attempt was made to supply "precious" data for memory that is
    /// already present in a memory object.
    pub const KERN_MEMORY_PRESENT: KernelCode = 23;
    /// A page was requested of a memory manager via memory_object_data_request
    /// for an object using a MEMORY_OBJECT_COPY_CALL strategy, with the
    /// VM_PROT_WANTS_COPY flag being used to specify that the page desired is
    /// for a copy of the object, and the memory manager has detected the page
    /// was pushed into a copy of the object while the kernel was walking the
    /// shadow chain from the copy to the object. This error code is delivered
    /// via memory_object_data_error and is handled by the kernel (it forces
    /// the kernel to restart the fault). It will not be seen by users.
    pub const KERN_MEMORY_DATA_MOVED: KernelCode = 24;
    /// A strategic copy was attempted of an object upon which a quicker copy is
    /// now possible. The caller should retry the copy using vm_object_copy_quickly.
    /// This error code is seen only by the kernel.
    pub const KERN_MEMORY_RESTART_COPY: KernelCode = 25;
    /// An argument applied to assert processor set privilege was not a
    /// processor set control port.
    pub const KERN_INVALID_PROCESSOR_SET: KernelCode = 26;
    /// The specified scheduling attributes exceed the thread's limits.
    pub const KERN_POLICY_LIMIT: KernelCode = 27;
    /// The specified scheduling policy is not currently enabled for the processor set.
    pub const KERN_INVALID_POLICY: KernelCode = 28;
    /// The external memory manager failed to initialize the memory object.
    pub const KERN_INVALID_OBJECT: KernelCode = 29;
    /// A thread is attempting to wait for an event for which there is
    /// already a waiting thread.
    pub const KERN_ALREADY_WAITING: KernelCode = 30;
    /// An attempt was made to destroy the default processor set.
    pub const KERN_DEFAULT_SET: KernelCode = 31;
    /// An attempt was made to fetch an exception port that is protected,
    /// or to abort a thread while processing a protected exception.
    pub const KERN_EXCEPTION_PROTECTED: KernelCode = 32;
    /// A ledger was required but not supplied.
    pub const KERN_INVALID_LEDGER: KernelCode = 33;
    /// The port was not a memory cache control port.
    pub const KERN_INVALID_MEMORY_CONTROL: KernelCode = 34;
    /// An argument supplied to assert security privilege was not a host security port.
    pub const KERN_INVALID_SECURITY: KernelCode = 35;
    /// thread_depress_abort was called on a thread which was not currently depressed.
    pub const KERN_NOT_DEPRESSED: KernelCode = 36;
    /// Object has been terminated and is no longer available
    pub const KERN_TERMINATED: KernelCode = 37;
    /// Lock set has been destroyed and is no longer available.
    pub const KERN_LOCK_SET_DESTROYED: KernelCode = 38;
    /// The thread holding the lock terminated before releasing the lock
    pub const KERN_LOCK_UNSTABLE: KernelCode = 39;
    /// The lock is already owned by another thread
    pub const KERN_LOCK_OWNED: KernelCode = 40;
    /// The lock is already owned by the calling thread
    pub const KERN_LOCK_OWNED_SELF: KernelCode = 41;
    /// Semaphore has been destroyed and is no longer available.
    pub const KERN_SEMAPHORE_DESTROYED: KernelCode = 42;
    /// Return from RPC indicating the target server was terminated before
    /// it successfully replied
    pub const KERN_RPC_SERVER_TERMINATED: KernelCode = 43;
    /// Terminate an orphaned activation.
    pub const KERN_RPC_TERMINATE_ORPHAN: KernelCode = 44;
    /// Allow an orphaned activation to continue executing.
    pub const KERN_RPC_CONTINUE_ORPHAN: KernelCode = 45;
    /// Empty thread activation (No thread linked to it)
    pub const KERN_NOT_SUPPORTED: KernelCode = 46;
    /// Remote node down or inaccessible.
    pub const KERN_NODE_DOWN: KernelCode = 47;
    /// A signalled thread was not actually waiting.
    pub const KERN_NOT_WAITING: KernelCode = 48;
    /// Some thread-oriented operation (semaphore_wait) timed out
    pub const KERN_OPERATION_TIMED_OUT: KernelCode = 49;
    /// During a page fault, indicates that the page was rejected as a
    /// result of a signature check.
    pub const KERN_CODESIGN_ERROR: KernelCode = 50;
    /// The requested property cannot be changed at this time.
    pub const KERN_POLICY_STATIC: KernelCode = 51;
    /// The provided buffer is of insufficient size for the requested data.
    pub const KERN_INSUFFICIENT_BUFFER_SIZE: KernelCode = 52;

    /// Converts the `KernelCode` into the most appropriate message `str`.
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        use std::ffi::CStr;
        use std::os::raw::c_char;

        extern "C" {
            fn mach_error_string(code: KernelCode) -> *const c_char;
        }

        unsafe { CStr::from_ptr(mach_error_string(self.0)) }.to_str()
    }

    /// Converts the `KernelCode` into the most appropriate `std::io::ErrorKind`.
    pub fn kind(&self) -> io::ErrorKind {
        match self.0 {
            Self::KERN_PROTECTION_FAILURE
            | Self::KERN_NO_ACCESS
            | Self::KERN_NOT_RECEIVER
            | Self::KERN_EXCEPTION_PROTECTED => io::ErrorKind::PermissionDenied,

            Self::KERN_RPC_SERVER_TERMINATED | Self::KERN_RPC_TERMINATE_ORPHAN => {
                io::ErrorKind::ConnectionAborted
            }

            Self::KERN_NAME_EXISTS
            | Self::KERN_RIGHT_EXISTS
            | Self::KERN_MEMORY_PRESENT
            | Self::KERN_ALREADY_WAITING => io::ErrorKind::AlreadyExists,

            Self::KERN_INVALID_ADDRESS
            | Self::KERN_INVALID_ARGUMENT
            | Self::KERN_INVALID_CAPABILITY
            | Self::KERN_INVALID_HOST
            | Self::KERN_INVALID_LEDGER
            | Self::KERN_INVALID_MEMORY_CONTROL
            | Self::KERN_INVALID_NAME
            | Self::KERN_INVALID_OBJECT
            | Self::KERN_INVALID_POLICY
            | Self::KERN_INVALID_PROCESSOR_SET
            | Self::KERN_INVALID_RIGHT
            | Self::KERN_INVALID_SECURITY
            | Self::KERN_INVALID_TASK
            | Self::KERN_INVALID_VALUE
            | Self::KERN_NO_SPACE
            | Self::KERN_MEMORY_FAILURE
            | Self::KERN_ALREADY_IN_SET
            | Self::KERN_NOT_IN_SET
            | Self::KERN_DEFAULT_SET
            | Self::KERN_NOT_DEPRESSED
            | Self::KERN_UREFS_OVERFLOW
            | Self::KERN_POLICY_LIMIT
            | Self::KERN_LOCK_SET_DESTROYED
            | Self::KERN_LOCK_UNSTABLE
            | Self::KERN_LOCK_OWNED
            | Self::KERN_LOCK_OWNED_SELF
            | Self::KERN_SEMAPHORE_DESTROYED
            | Self::KERN_NOT_SUPPORTED
            | Self::KERN_NOT_WAITING
            | Self::KERN_INSUFFICIENT_BUFFER_SIZE => io::ErrorKind::InvalidInput,

            Self::KERN_MEMORY_ERROR
            | Self::KERN_NODE_DOWN
            | Self::KERN_CODESIGN_ERROR
            | Self::KERN_POLICY_STATIC => io::ErrorKind::InvalidData,

            Self::KERN_OPERATION_TIMED_OUT => io::ErrorKind::TimedOut,

            _ => io::ErrorKind::Other,
        }
    }
}

impl error::Error for KernelError {}

impl fmt::Debug for KernelError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("KernelError")
            .field("code", &self.0)
            .field("message", &self.to_str().unwrap_or("invalid kernel error"))
            .finish()
    }
}

impl fmt::Display for KernelError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.to_str() {
            Err(err) => write!(fmt, "invalid kernel error {} ({})", self.0, err),
            Ok(val) => write!(fmt, "{} (kernel error {})", val, self.0),
        }
    }
}

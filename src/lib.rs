//! A memory reading library for reading data from `/proc/<pid>/mem` with
//! memory layout awareness from `/proc/<pid>/maps`

#![feature(new_uninit)]

#[cfg(not(target_os = "linux"))]
compile_error!("libprocmem only supported for Linux targets");

use std::fs::File;
use std::io::{Seek, SeekFrom, Read};
use std::mem::MaybeUninit;

/// Wrapper type around `Result`
pub type Result<T> = std::result::Result<T, Error>;

/// Errors for this module
pub enum Error {
    /// Failed to open `/proc/<pid>/mem`
    OpenMem(usize, std::io::Error),

    /// Failed to read `/proc/<pid>/mem`
    ReadMem(usize, std::io::Error),

    /// Failed to read `/proc/<pid>/maps`
    ReadMaps(usize, std::io::Error),

    /// Failed to convert read string to UTF-8
    InvalidString(usize, std::string::FromUtf8Error),

    /// Failed to parse `/proc/<pid>/maps`
    ParseMaps(usize),
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::OpenMem(pid, e) =>
                write!(f, "Failed to open memory for pid {pid}: {e}")?,
            Error::ReadMem(pid, e) =>
                write!(f, "Failed to read memory for pid {pid}: {e}")?,
            Error::ReadMaps(pid, e) =>
                write!(f, "Failed to read maps for pid {pid}: {e}")?,
            Error::InvalidString(pid, e) =>
                write!(f, "Failed to convert bytes to UTF-8 data \
                          for pid {pid}: {e}")?,
            Error::ParseMaps(pid) => 
                write!(f, "Failed to parse maps for pid {pid}")?,
        }

        Ok(())
    }
}

/// An instance of the memory reader
pub struct Memory {
    /// PID we attached to
    pid: usize,

    /// Wrapper around the readable memory for the process
    mem: File,
}

/// Info about a memory mapping
pub struct Mapping {
    /// Start address of the mapping
    pub base: u64,

    /// End address of the mapping, such that `end - base` is the number of
    /// bytes in the mapping
    pub end: u64,

    /// Memory is readable
    pub r: bool,

    /// Memory is writable
    pub w: bool,

    /// Memory is executable
    pub x: bool,
}

impl Memory {
    /// Create a [`Memory`] instance from a process with a running PID
    pub fn pid(pid: usize) -> Result<Self> {
        // Open the memory mapping
        let mem = File::open(format!("/proc/{}/mem", pid))
            .map_err(|x| Error::OpenMem(pid, x))?;

        Ok(Self {
            pid,
            mem,
        })
    }

    /// Read a null terminated string at a given address, doesn't include the
    /// null-terminator in the returned string as it's converted to a Rust
    /// string
    pub fn read_nul_string(&mut self, addr: u64) -> Result<String> {
        // Create storage for the resut
        let mut bytes = Vec::new();

        // Read one byte at a time. Slow, but you're working with strings, you
        // don't care about perf anyways
        for addr in addr.. {
            let byte = self.read::<u8>(addr)?;
            if byte == 0 {
                break;
            }

            bytes.push(byte);
        }

        // Convert the string
        Ok(String::from_utf8(bytes).map_err(|x| {
            Error::InvalidString(self.pid, x)
        })?)
    }

    /// Query the address space information from `/proc/<pid>/maps`
    pub fn query_address_space(&mut self) -> Result<Vec<Mapping>> {
        // Output
        let mut ret = Vec::new();

        // Read the memory map
        let maps = std::fs::read_to_string(
            format!("/proc/{}/maps", self.pid))
            .map_err(|x| Error::ReadMaps(self.pid, x))?;

        for line in maps.lines() {
            // Split the main line by spaces
            let mut spl = line.split(" ");
            let addr_range = spl.next()
                .ok_or(Error::ParseMaps(self.pid))?;
            let perms = spl.next()
                .ok_or(Error::ParseMaps(self.pid))?;

            // Parse addresses
            let mut spl = addr_range.split("-");
            let base = u64::from_str_radix(spl.next()
                .ok_or(Error::ParseMaps(self.pid))?, 16)
                .map_err(|_| Error::ParseMaps(self.pid))?;
            let end = u64::from_str_radix(spl.next()
                .ok_or(Error::ParseMaps(self.pid))?, 16)
                .map_err(|_| Error::ParseMaps(self.pid))?;

            // Parse permissions
            let r = perms.get(0..1) == Some("r");
            let w = perms.get(1..2) == Some("w");
            let x = perms.get(2..3) == Some("x");

            // Log the memory
            ret.push(Mapping { base, end, r, w, x });
        }

        Ok(ret)
    }

    /// Read a `T` from memory at `addr`
    pub fn read<T: Pod>(&mut self, addr: u64) -> Result<T> {
        // Create return value
        let mut ret: MaybeUninit<T> = MaybeUninit::uninit();

        // Seek to the location to read
        self.mem.seek(SeekFrom::Start(addr))
            .map_err(|x| Error::ReadMem(self.pid, x))?;

        // Attempt to read the memory
        let ptr = unsafe {
            core::slice::from_raw_parts_mut(
                ret.as_mut_ptr() as *mut u8, core::mem::size_of_val(&ret))
        };
        self.mem.read_exact(ptr)
            .map_err(|x| Error::ReadMem(self.pid, x))?;

        Ok(unsafe { ret.assume_init() })
    }

    /// Read a `[T]` from memory at `addr` containing `elements`
    pub fn read_slice<T: Pod>(&mut self, addr: u64, elements: usize)
            -> Result<Box<[T]>> {
        // Create return value
        let mut ret: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(elements);

        // Seek to the location to read
        self.mem.seek(SeekFrom::Start(addr))
            .map_err(|x| Error::ReadMem(self.pid, x))?;

        // Attempt to read the memory
        let ptr = unsafe {
            core::slice::from_raw_parts_mut(
                ret.as_mut_ptr() as *mut u8, core::mem::size_of_val(&*ret))
        };
        self.mem.read_exact(ptr)
            .map_err(|x| Error::ReadMem(self.pid, x))?;

        Ok(unsafe { ret.assume_init() })
    }
}

/// Marker trait for plain-old-data which can be copied directly between other
/// Pod types by copying the underlying bytes
///
/// This is only safe to implement on repr-C structures with no padding bytes
/// and consisting only of fields which are also `Pod`
pub unsafe trait Pod: Copy + Sync + Send + 'static {}

unsafe impl Pod for i8    {}
unsafe impl Pod for i16   {}
unsafe impl Pod for i32   {}
unsafe impl Pod for i64   {}
unsafe impl Pod for i128  {}
unsafe impl Pod for isize {}
unsafe impl Pod for u8    {}
unsafe impl Pod for u16   {}
unsafe impl Pod for u32   {}
unsafe impl Pod for u64   {}
unsafe impl Pod for u128  {}
unsafe impl Pod for usize {}
unsafe impl Pod for f32   {}
unsafe impl Pod for f64   {}

unsafe impl<const N: usize> Pod for [i8;    N] {}
unsafe impl<const N: usize> Pod for [i16;   N] {}
unsafe impl<const N: usize> Pod for [i32;   N] {}
unsafe impl<const N: usize> Pod for [i64;   N] {}
unsafe impl<const N: usize> Pod for [i128;  N] {}
unsafe impl<const N: usize> Pod for [isize; N] {}
unsafe impl<const N: usize> Pod for [u8;    N] {}
unsafe impl<const N: usize> Pod for [u16;   N] {}
unsafe impl<const N: usize> Pod for [u32;   N] {}
unsafe impl<const N: usize> Pod for [u64;   N] {}
unsafe impl<const N: usize> Pod for [u128;  N] {}
unsafe impl<const N: usize> Pod for [usize; N] {}
unsafe impl<const N: usize> Pod for [f32;   N] {}
unsafe impl<const N: usize> Pod for [f64;   N] {}


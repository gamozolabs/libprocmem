# Summary

A very simple library that wraps around `/proc/pid/mem` and `/proc/pid/maps`
to read memory out of a running process on Linux.

# Usage

Basic usage looks like:

```rust
// Request access to PID `1234`'s memory
let mem = Memory::pid(1234)?;

/// Read some data!
let data = mem.read::<u32>(0x13370000)?;

/// Read a slice of 69 floats
let data = mem.read_slice::<f32>(0x13370000, 69)?;
```


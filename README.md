# `aligned`

A Rust library that ensures a pointer is aligned correctly before dereferencing it.

This library contains unsafe functions defined in `core::ptr` and `core::slice` (except `read_unaligned` and `write_unaligned`). All functions defined in this crate check whether the passed pointers are aligned correctly and not null.

This crate is intended to prevent from dereferencing to the unaligned address. For example the below code example panics because `p` points to an unaligned address. If we import `core::ptr` instead of `aligned::ptr`, this code may run successfully. However, reading a value from unaligned pointer causes *undefined behavior* (except `read_unaligned`).

This crate supports the `no_std` environment.

```rust
use aligned::ptr;

fn main() {
    let x = 0xdeadbeaf_u32;
    let p = (&x as *const u32 as usize + 1) as *const u16;

    unsafe { ptr::read(p) };
}
```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

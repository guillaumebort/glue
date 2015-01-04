# A "Dynamic Assembler" for rust

This is a very experimental project. The current goals are:

- Find a way to encode assembly instructions directly in the host language (rust).
- Provide lazy functions with on-demand compilation.
- Allow functions re-compilation, for further optimization.
- Provide more high level features to build a JIT Compiler (at least registers allocation).

> NOTE: the opcode support is far from complete (it currently only provides encoders for a few opcodes and addressing modes that useful enough to work on other aspects of the assembler) 

## "Hello World" (MacOS X 64bits) 

```rust
let jit = Jit::new();

let mut f = jit.create_function("hello_world".to_string());
let msg = "Hello World!\n";

f.code([
  mov(rax, 0x2000004u),
  mov(rdx, msg.len()),
  mov(rsi, msg.as_ptr()),
  mov(rdi, 1u),
  syscall(),
  ret()
]);

println!("{}", f.dump())

let hello_world = jit_fn!(f, () -> ());

hello_world();
```

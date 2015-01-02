#[macro_export]
macro_rules! jit_fn (
  ($jit_function:ident, ($($arg_type:ty),*) -> $return_type:ty) => (
    unsafe {
      let f: extern "C" fn($($arg_type),*) -> $return_type = std::mem::transmute($jit_function.compile());
      f
    }
  )
)

macro_rules! jit_lazy_fn (
  ($jit_function:ident, ($($arg_type:ty),*) -> $return_type:ty, $jit_compiler:ident) => (
    unsafe {
      let f: extern "C" fn($($arg_type),*) -> $return_type = std::mem::transmute($jit_function.lazy($jit_compiler));
      f
    }
  )
)
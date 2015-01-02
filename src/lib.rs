#![crate_name = "glue"]
#![crate_type = "rlib"]
#![feature(if_let, globs, macro_rules)]

pub use self::backend::*;

use std::os;
use std::ptr;
use std::mem;
use std::sync::Arc;
use std::sync::RWLock;
use std::collections::HashMap;

#[cfg(target_arch = "x86_64")]
#[path = "assembler/x86_64.rs"]
pub mod backend;

mod macros;

pub struct JitFunction {
  name: String,
  code: Vec<(Vec<Instruction>, Option<String>)>,
  jit: Arc<Jit>
}

impl JitFunction {

  pub fn code(&mut self, code: &[Instruction]) {
    self.code.push((code.to_vec(), None));
  }

  #[allow(dead_code)]
  pub fn dump(&self) -> String {
    let mut string = format!("{}:\n", self.name);
    let mut address = 0;
    for &(ref instructions, _) in self.code.iter() {
      for instruction in instructions.iter() {
        let op_code = instruction.to_opcode();
        let bytes_len = op_code.bytes.len();
        let lines = bytes_len / 7 + (if bytes_len > 7 && bytes_len % 7 > 0 { 1 } else { 0 });
        for l in range(0, std::cmp::max(1, lines)) {
          let mut bytes = String::new();
          for byte in op_code.bytes.slice(l * 7, std::cmp::min((l + 1) * 7, bytes_len)).iter() {
            bytes.push_str(format!("{:02x} ", *byte).as_slice());
          }
          string.push_str(format!("\t{:016x}:\t{:24s}", address, bytes).as_slice());
          if l == 0 {
            string.push_str(format!("{}", op_code).as_slice());
          }
          string.push_str("\n");
          address = address + op_code.bytes.len();
        }
      }
    }
    string
  }

  pub fn compile(self) -> *const u8 {
    let mut bytes = vec![];
    for &(ref block, _) in self.code.iter() {
      for insn in block.iter() {
        bytes.extend(insn.to_opcode().bytes.into_iter());
      }
    }
    let mut jit_internal = self.jit.internal.write();
    unsafe {
      let function_pointer = jit_internal.allocate_memory(bytes.len());
      jit_internal.call_sites.insert(self.name, function_pointer.clone());
      ptr::copy_memory(function_pointer, bytes.as_ptr(), bytes.len());
      mem::transmute(function_pointer)
    }
  }

  pub fn lazy(self, compiler: fn (&mut JitFunction) -> ()) -> *const u8 {
    fail!()
  }

}

pub struct Jit {
  internal: RWLock<JitInternal>
}

static PAGE_SIZE: uint = 4096;

impl Jit {

  pub fn new() -> Arc<Jit> {
    Arc::new(Jit {
      internal: RWLock::new(JitInternal {
        memory_pages: vec![MemoryRegion::new(PAGE_SIZE)],
        call_sites: HashMap::new()
      })
    })
  }

}

struct JitInternal {
  memory_pages: Vec<MemoryRegion>,
  call_sites: HashMap<String,*mut u8>
}

impl JitInternal {

  unsafe fn allocate_memory(&mut self, bytes: uint) -> *mut u8 {
    if self.memory_pages.last().unwrap().left_space() < bytes {
      self.memory_pages.push(MemoryRegion::new(PAGE_SIZE));
    }
    self.memory_pages.last_mut().unwrap().allocate(bytes)
  }

}

pub trait JitFactory {
  fn create_function(&self, name: String) -> JitFunction;
}

impl JitFactory for Arc<Jit> {

  fn create_function(&self, name: String) -> JitFunction {
    let mut jit_internal = self.internal.write();
    if jit_internal.call_sites.contains_key(&name) {
      fail!("Jit Function {} already defined", name)
    }
    jit_internal.call_sites.insert(name.clone(), 0 as *mut u8);
    JitFunction {
      name: name,
      code: vec![],
      jit: self.clone()
    }
  }

}

fn trampoline() -> Vec<Instruction> {
  fail!()
}

struct MemoryRegion {
  mem: os::MemoryMap,
  allocation_pointer: uint
}

impl MemoryRegion {

  fn new(bytes: uint) -> MemoryRegion {
    MemoryRegion {
      mem: os::MemoryMap::new(bytes, [os::MapReadable, os::MapWritable, os::MapExecutable]).unwrap(),
      allocation_pointer: 0
    }
  }

  fn left_space(&self) -> uint {
    self.mem.len() - self.allocation_pointer
  }

  unsafe fn allocate(&mut self, bytes: uint) -> *mut u8 {
    let ptr = self.mem.data().offset(self.allocation_pointer as int);
    self.allocation_pointer += bytes;
    if self.allocation_pointer > self.mem.len() {
      fail!()
    }
    ptr
  }

}
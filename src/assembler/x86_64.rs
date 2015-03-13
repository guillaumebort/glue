use std::ops;
use std::fmt;
use std::old_io::extensions;

#[derive(Clone,Debug)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub enum Register {
  rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp, r8, r9, r10, r11, r12, r13, r14, r15,
  eax, ebx, ecx, edx, esi, edi, ebp, esp, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d,
  ax, bx, cx, dx, sp, bp, si, di, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w,
  al, bl, cl, dl, ah, ch, dh, bh, r8l, r9l, r10l, r11l, r12l, r13l, r14l, r15l
}

#[derive(Clone)]
pub enum Operand {
  RegisterDirect(Register), // r64
  MemoryDirect(u64), // [imm64]
  MemoryRegisterIndirect(Register), // [r64]
  MemoryBased(Register,i64), // [r64 (+|-) imm64]
  MemoryBasedIndexed(Register,Register,i64), // [r64 + r64 (+|-) imm64]
  MemoryIndexed(Register,u8,i64), // [r64 * (1|2|4|8) (+|-) imm64]
  MemoryBasedIndexedScale(Register,Register,u8,i64), // [r64 + r64 * (1|2|4|8) + (+|-) imm64]
  Immediate(uint,u8) // imm64|imm32|imm16|imm8
}

impl fmt::Show for Operand {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use std::num;
    match self {
      &Operand::RegisterDirect(reg) => write!(f, "{}", reg),
      &Operand::MemoryDirect(disp) => write!(f, "[0x{:x}]", disp),
      &Operand::MemoryRegisterIndirect(reg) => write!(f, "[{}]", reg),
      &Operand::MemoryBased(reg, disp) if disp == 0 => write!(f, "[{}]", reg),
      &Operand::MemoryBased(reg, disp) if disp < 0 => write!(f, "[{} - {}]", reg, num::abs(disp)),
      &Operand::MemoryBased(reg, disp) => write!(f, "[{} + {}]", reg, num::abs(disp)),
      &Operand::MemoryBasedIndexed(reg1, reg2, disp) if disp == 0 => write!(f, "[{} + {}]", reg1, reg2),
      &Operand::MemoryBasedIndexed(reg1, reg2, disp) if disp < 0 => write!(f, "[{} + {} - {}]", reg1, reg2, num::abs(disp)),
      &Operand::MemoryBasedIndexed(reg1, reg2, disp) => write!(f, "[{} + {} + {}]", reg1, reg2, num::abs(disp)),
      &Operand::MemoryIndexed(reg, scale, disp) if disp == 0 => write!(f, "[{} * {}]", reg, scale),
      &Operand::MemoryIndexed(reg, scale, disp) if disp < 0 => write!(f, "[{} * {} - {}]", reg, scale, num::abs(disp)),
      &Operand::MemoryIndexed(reg, scale, disp) => write!(f, "[{} * {} + {}]", reg, scale, num::abs(disp)),
      &Operand::MemoryBasedIndexedScale(reg1, reg2, scale, disp) if disp == 0 => write!(f, "[{} + {} * {}]", reg1, reg2, scale),
      &Operand::MemoryBasedIndexedScale(reg1, reg2, scale, disp) if disp < 0 => write!(f, "[{} + {} * {} - {}]", reg1, reg2, scale, num::abs(disp)),
      &Operand::MemoryBasedIndexedScale(reg1, reg2, scale, disp) => write!(f, "[{} + {} * {} + {}]", reg1, reg2, scale, num::abs(disp)),
      &Operand::Immediate(v, _) => write!(f, "0x{:x}", v)
    }
  }
}

#[derive(Clone)]
pub enum Instruction {
  Add(Operand,Operand),
  Mov(Operand,Operand),
  Push(Operand),
  Ret,
  Syscall
}

impl Instruction {
  pub fn to_opcode(&self) -> OpCode {

    let missing_encoder = || panic!("Missing encoder for {}", self);

    let encode_rex = |size:uint, r1_extended:Option<bool>, r2_extended:Option<bool>| -> Option<u8> {
      let mut rex = 0b01000000u8;
      if size == 8 { rex += 1 << 3; }
      match r1_extended { Some(true) => rex += 1 << 0, _ => () }
      match r2_extended { Some(true) => rex += 1 << 2, _ => () }
      match rex { 0x40 => None, _ => Some(rex) }
    };

    let bytes = match self {

      &Add(RegisterDirect(r1), Immediate(imm, _)) => {
        match (r1.encode(), size_in_bytes(imm)) {
          ((r1_code, r1_size, r1_extended), 1) if r1_size >= 2 => {
            let mut bytes = vec![];
            match encode_rex(r1_size, Some(r1_extended), None) {
              Some(rex) => bytes.push(rex),
              _ => ()
            };
            bytes.push(0x83);
            bytes.push(0b11000000 + r1_code);
            bytes.push(imm as u8);
            bytes
          },
          _ => missing_encoder()
        }
      }
      
      &Mov(RegisterDirect(r1), RegisterDirect(r2)) => {
        match (r1.encode(), r2.encode()) {
          ((r1_code, r1_size, r1_extended), (r2_code, r2_size, r2_extended)) if r1_size == r2_size && r1_size >= 4 => {
            let mut bytes = vec![];
            match encode_rex(r1_size, Some(r1_extended), Some(r2_extended)) {
              Some(rex) => bytes.push(rex),
              _ => ()
            };
            bytes.push(0x89);
            bytes.push(0b11000000 + (r2_code << 3) + r1_code);
            bytes
          }
          _ => missing_encoder()
        }
      }

      &Mov(RegisterDirect(reg), Immediate(imm, imm_size)) if imm_size <= 4 => {
        match reg.encode() {
          (reg_code, reg_size, reg_extended) if reg_size > 2 => {
            let mut bytes = vec![];
            match encode_rex(reg_size, Some(reg_extended), None) {
              Some(rex) => bytes.push(rex),
              _ => ()
            };
            bytes.push(0xc7);
            bytes.push(0b11000000 + reg_code);
            bytes.extend(extensions::u64_to_le_bytes(imm as u64, 4u, |v| v.to_vec()).into_iter());
            bytes
          }
          _ => missing_encoder()
        }
      }

      &Mov(RegisterDirect(reg), Immediate(imm, imm_size)) if imm_size == 8 => {
        match reg.encode() {
          (reg_code, reg_size, reg_extended) if reg_size > 2 => {
            let mut bytes = vec![];
            match encode_rex(reg_size, Some(reg_extended), None) {
              Some(rex) => bytes.push(rex),
              _ => ()
            };
            bytes.push(0xb8 + reg_code);
            bytes.extend(extensions::u64_to_le_bytes(imm as u64, 8u, |v| v.to_vec()).into_iter());
            bytes
          }
          _ => missing_encoder()
        }
      }

      &Ret => {
        vec![0xc3]
      }

      &Syscall => {
        vec![0x0f, 0x05]
      }

      _ => missing_encoder()
    };

    OpCode {
      bytes: bytes,
      instruction: self
    }
  }
}

pub struct OpCode<'a> {
  pub bytes: Vec<u8>,
  pub instruction: &'a Instruction
}

impl<'_> fmt::Show for OpCode<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.instruction)
  }
}

impl fmt::Show for Instruction {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      &Add(o1,o2) => write!(f, "add     {}, {}", o1, o2),
      &Mov(o1,o2) => write!(f, "mov     {}, {}", o1, o2),
      &Push(o1)   => write!(f, "push    {}", o1),
      &Ret => write!(f, "ret"),
      &Syscall => write!(f, "syscall")
    }
  }
}

pub trait Parameter {
  fn to_operand(&self) -> Operand;
}

impl Parameter for Register {
  fn to_operand(&self) -> Operand { 
    RegisterDirect(*self) 
  }
}

impl Parameter for uint {
  fn to_operand(&self) -> Operand { 
    Immediate(*self as uint, {
      if size_in_bytes(*self) <= 4 {
        4
      } else {
        8
      }
    }) 
  }
}

impl Parameter for u64 {
  fn to_operand(&self) -> Operand { 
    Immediate(*self as uint, 8) 
  }
}

impl Parameter for u32 {
  fn to_operand(&self) -> Operand { 
    Immediate(*self as uint, 4) 
  }
}

impl Parameter for u16 {
  fn to_operand(&self) -> Operand { 
    Immediate(*self as uint, 2) 
  }
}

impl Parameter for u8 {
  fn to_operand(&self) -> Operand { 
    Immediate(*self as uint, 1) 
  }
}

impl Parameter for [Register; 1] {
  fn to_operand(&self) -> Operand { 
    MemoryRegisterIndirect(self[0]) 
  }
}

impl Parameter for [u64; 1] {
  fn to_operand(&self) -> Operand { 
    MemoryDirect(self[0]) 
  }
}

impl<'a, A> Parameter for &'a A {
  fn to_operand(&self) -> Operand {
    use std::mem;
    MemoryDirect(unsafe { mem::transmute::<&A,u64>(*self) })
  }
}

impl<A> Parameter for *const A {
  fn to_operand(&self) -> Operand {
    Immediate(*self as uint, 8) 
  }
}

impl Parameter for [Operand; 1] {
  fn to_operand(&self) -> Operand {
    self[0]
  }
}

pub trait RegisterRhs<S> {
  fn add_to_register(&self, lhs: &Register) -> S;
}

impl<S, R> ops::Add<R, S> for Register where R: RegisterRhs<S> {
  fn add(&self, rhs: &R) -> S {
    rhs.add_to_register(self)
  }
}

impl RegisterRhs<Operand> for int {
  fn add_to_register(&self, lhs: &Register) -> Operand {
    MemoryBased(*lhs, *self as i64)
  }
}

impl RegisterRhs<Operand> for Register {
  fn add_to_register(&self, lhs: &Register) -> Operand {
    MemoryBasedIndexed(*lhs, *self, 0)
  }
}

impl RegisterRhs<Operand> for Operand {
  fn add_to_register(&self, lhs: &Register) -> Operand {
    match self {
      &MemoryIndexed(index, scale, disp) => MemoryBasedIndexedScale(*lhs, index, scale, disp),
      _ => panic!("Unsupported operation {} + {}", lhs, self)
    }
  }
}

impl ops::Sub<int, Operand> for Register  {
  fn sub(&self, rhs: &int) -> Operand {
    MemoryBased(*self, -*rhs as i64)
  }
}

impl ops::Add<int, Operand> for Operand  {
  fn add(&self, rhs: &int) -> Operand {
    match self {
      &MemoryBasedIndexed(base, index, disp) => MemoryBasedIndexed(base, index, disp + *rhs as i64),
      &MemoryIndexed(index, scale, disp) => MemoryIndexed(index, scale, disp + *rhs as i64),
      &MemoryBasedIndexedScale(base, index, scale, disp) => MemoryBasedIndexedScale(base, index, scale, disp + *rhs as i64),
      _ => panic!("Unsupported operation {} + {}", self, rhs)
    }
  }
}

impl ops::Sub<int, Operand> for Operand  {
  fn sub(&self, rhs: &int) -> Operand {
    match self {
      &MemoryBasedIndexed(base, index, disp) => MemoryBasedIndexed(base, index, disp - *rhs as i64),
      &MemoryIndexed(index, scale, disp) => MemoryIndexed(index, scale, disp - *rhs as i64),
      &MemoryBasedIndexedScale(base, index, scale, disp) => MemoryBasedIndexedScale(base, index, scale, disp - *rhs as i64),
      _ => panic!("Unsupported operation {} - {}", self, rhs)
    }
  }
}

impl ops::Mul<uint, Operand> for Register  {
  fn mul(&self, rhs: &uint) -> Operand {
    match *rhs {
      1 | 2 | 4 | 8 => MemoryIndexed(*self, *rhs as u8, 0),
      _ => panic!("Scaling factor must be either 1|2|4|8")
    }
    
  }
}

#[allow(dead_code)]
pub fn push<A: Parameter>(a: A) -> Instruction {
  Push(a.to_operand())
}

#[allow(dead_code)]
pub fn mov<A: Parameter, B: Parameter>(a: A, b: B) -> Instruction {
  Mov(a.to_operand(), b.to_operand())
}

#[allow(dead_code)]
pub fn add<A: Parameter, B: Parameter>(a: A, b: B) -> Instruction {
  Add(a.to_operand(), b.to_operand())
}

#[allow(dead_code)]
pub fn ret() -> Instruction {
  Ret
}

#[allow(dead_code)]
pub fn syscall() -> Instruction {
  Syscall
}

fn size_in_bytes(num: uint) -> uint {
  use std::u8;
  use std::u16;
  use std::u32;
  use std::u64;

  if num <= u8::MAX as uint { 1 } 
  else if num <= u16::MAX as uint { 2 } 
  else if num <= u32::MAX as uint { 4 } 
  else if num <= u64::MAX as uint { 8 } else {
    unreachable!()
  }
}

impl Register {
  fn encode(&self) -> (u8,uint,bool) {
    match self {
      // 64 bits
      &rax  => (0b000, 8, false),
      &rbx  => (0b011, 8, false),
      &rcx  => (0b001, 8, false),
      &rdx  => (0b010, 8, false),
      &rsi  => (0b110, 8, false),
      &rdi  => (0b111, 8, false),
      &rbp  => (0b101, 8, false),
      &rsp  => (0b100, 8, false),
      &r8   => (0b000, 8, true),
      &r9   => (0b001, 8, true),
      &r10  => (0b010, 8, true),
      &r11  => (0b011, 8, true),
      &r12  => (0b100, 8, true),
      &r13  => (0b101, 8, true),
      &r14  => (0b110, 8, true),
      &r15  => (0b111, 8, true),

      // 32 bits
      &eax  => (0b000, 4, false),
      &ebx  => (0b011, 4, false),
      &ecx  => (0b001, 4, false),
      &edx  => (0b010, 4, false),
      &esi  => (0b110, 4, false),
      &edi  => (0b111, 4, false),
      &ebp  => (0b101, 4, false),
      &esp  => (0b100, 4, false),
      &r8d  => (0b000, 4, true),
      &r9d  => (0b001, 4, true),
      &r10d => (0b010, 4, true),
      &r11d => (0b011, 4, true),
      &r12d => (0b100, 4, true),
      &r13d => (0b101, 4, true),
      &r14d => (0b110, 4, true),
      &r15d => (0b111, 4, true),

      // 16 bits
      &ax   => (0b000, 2, false),
      &bx   => (0b011, 2, false),
      &cx   => (0b001, 2, false),
      &dx   => (0b010, 2, false),
      &si   => (0b110, 2, false),
      &di   => (0b111, 2, false),
      &bp   => (0b101, 2, false),
      &sp   => (0b100, 2, false),
      &r8w  => (0b000, 2, true),
      &r9w  => (0b001, 2, true),
      &r10w => (0b010, 2, true),
      &r11w => (0b011, 2, true),
      &r12w => (0b100, 2, true),
      &r13w => (0b101, 2, true),
      &r14w => (0b110, 2, true),
      &r15w => (0b111, 2, true),

      // 8 bits
      &al   => (0b000, 1, false),
      &bl   => (0b011, 1, false),
      &cl   => (0b001, 1, false),
      &dl   => (0b010, 1, false),
      &dh   => (0b110, 1, false),
      &bh   => (0b111, 1, false),
      &ch   => (0b101, 1, false),
      &ah   => (0b100, 1, false),
      &r8l  => (0b000, 1, true),
      &r9l  => (0b001, 1, true),
      &r10l => (0b010, 1, true),
      &r11l => (0b011, 1, true),
      &r12l => (0b100, 1, true),
      &r13l => (0b101, 1, true),
      &r14l => (0b110, 1, true),
      &r15l => (0b111, 1, true)
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  fn assert_bytes(insn: Instruction, expected_bytes: &[u8]) {
    let actual_bytes = insn.to_opcode().bytes;

    if actual_bytes.as_slice() != expected_bytes {
      panic!("Wrong encoding for {}\nExpected {}, actually {}", insn, expected_bytes, actual_bytes.as_slice())
    }
  }

  #[test]
  pub fn syntax() {
    let var = 0x1ef578dd3caa7b99u64;
    let s = "coco".to_string();
    let ptr = ebx; 

    let _ = [
      push(rbp),
      mov(rsp, rbp),
      mov(0x0u32, eax),
      mov(eax, [ebx]),
      mov([var], ebx),
      mov(eax, ebx),
      mov(edi, &s),
      mov(eax, [esi + 4i]),
      mov(eax, [esi - 1024i]),
      mov(eax, [ebx + ebp]),
      mov(eax, [ebx + ebp + 8i]),
      mov(eax, [ebx + ebp + 8i + 16i]),
      mov(eax, [ebx + ebp - 1024i]),
      mov(esi, [ebp + 8i]),
      mov(esi, [eax * 2u]),
      mov(esi, [eax * 4u + 8i]),
      mov(esi, [eax * 4u - 1024i]),
      mov(esi, [ebx + eax * 8u]),
      mov(esi, [ebx + eax * 8u + 16i]),
      mov(esi, [ebx + eax * 8u - 1024i]),
      mov(eax, [ptr]),
      ret()
    ];
  }

  #[test]
  pub fn encoding() {

    // mov reg,reg
    assert_bytes( mov(rax, rdi),              [0x48, 0x89, 0xf8] );
    assert_bytes( mov(eax, edi),              [0x89, 0xf8] );
    assert_bytes( mov(rax, r10),              [0x4c, 0x89, 0xd0] );
    assert_bytes( mov(r11, rdi),              [0x49, 0x89, 0xfb] );
    assert_bytes( mov(r11d, edi),             [0x41, 0x89, 0xfb] );

    // add reg, imm
    assert_bytes( add(rax, 4u8),              [0x48, 0x83, 0xc0, 0x04] );

    // ret
    assert_bytes( ret(),                      [0xc3] );

    // mov reg, imm32
    assert_bytes( mov(rax, 0x2000004u),       [0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x02] );

    // mov reg, imm64
    assert_bytes( mov(rsi, 0x7fff56cf86d8u),  [0x48, 0xbe, 0xd8, 0x86, 0xcf, 0x56, 0xff, 0x7f, 0x00, 0x00] );

    // syscall
    assert_bytes( syscall(),                  [0x0f, 0x05] );

  }

}

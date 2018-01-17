#[macro_use]
extern crate bitflags;

extern crate byteorder;

use byteorder::{ByteOrder, NativeEndian};

type Reg = u64;

struct Cpu {
    mem: Vec<u8>,
    regs: Vec<Reg>,
    flags: CpuFlags,
    cycles: u64,
}

#[derive(Copy, Clone)]
enum MemSize {
    U1,
    U2,
    U4,
    U8,
}

#[derive(PartialEq, Debug, Copy, Clone)]
enum MemReg {
    U1(u8),
    U2(u16),
    U4(u32),
    U8(u64),
}

impl MemSize {
    fn len(self) -> usize {
        match self {
            MemSize::U1 => 1,
            MemSize::U2 => 2,
            MemSize::U4 => 4,
            MemSize::U8 => 8,
        }
    }
}

impl MemReg {
    fn len(self) -> usize {
        match self {
            MemReg::U1(_) => 1,
            MemReg::U2(_) => 2,
            MemReg::U4(_) => 4,
            MemReg::U8(_) => 8,
        }
    }

    fn size(self) -> MemSize {
        match self {
            MemReg::U1(_) => MemSize::U1,
            MemReg::U2(_) => MemSize::U2,
            MemReg::U4(_) => MemSize::U4,
            MemReg::U8(_) => MemSize::U8,
        }
    }
}


bitflags! {
    #[derive(Default)]
    struct CpuFlags: u8 {
        const RUNNING = 0b0000001;
        const SIGNED  = 0b0000010;
        const ZERO    = 0b0000100;
    }
}

impl Cpu {
    fn new(memsize: usize, regcount: usize) -> Cpu {
        Cpu {
            mem: vec![0; memsize],
            regs: vec![0; regcount],
            flags: CpuFlags::default(),
            cycles: 0,
        }
    }
}


impl Cpu {
    fn read_memory(&self, size: MemSize, index: usize) -> MemReg {
        let range = index .. (index + size.len());
        match size {
            MemSize::U1 => MemReg::U1(self.mem[index]),
            MemSize::U2 => MemReg::U2(NativeEndian::read_u16(&self.mem[range])),
            MemSize::U4 => MemReg::U4(NativeEndian::read_u32(&self.mem[range])),
            MemSize::U8 => MemReg::U8(NativeEndian::read_u64(&self.mem[range])),
        }
    }

    fn write_memory(&mut self, mem: MemReg, index: usize) {
        let range = index .. (index + mem.len());
        match mem {
            MemReg::U1(x) => self.mem[index] = x,
            MemReg::U2(x) => NativeEndian::write_u16(&mut self.mem[range], x),
            MemReg::U4(x) => NativeEndian::write_u32(&mut self.mem[range], x),
            MemReg::U8(x) => NativeEndian::write_u64(&mut self.mem[range], x),
        }
    }
}

fn main() {
    let mut cpu = Cpu::new(1 << 16, 8);

    // cpu.write_memory(MemSize::U4, 0, 0xffffffff);

    // println!("memory is {}", cpu.read_memory(MemSize::U4, 0));

    // for i in 0..4 {
    //     println!("memory at {} is: {}", i, cpu.read_memory(MemSize::U1, i));
    // }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_unsigned() {
        let mut cpu = Cpu::new(1024, 0);

        let tests = [
            MemReg::U1( u8::max_value()),
            MemReg::U2(u16::max_value()),
            MemReg::U4(u32::max_value()),
            MemReg::U8(u64::max_value()),
            MemReg::U1(0),
            MemReg::U2(0),
            MemReg::U4(0),
            MemReg::U8(0),
        ];

        for &r in tests.iter() {
            cpu.write_memory(r, 0);
            assert_eq!(cpu.read_memory(r.size(), 0), r);
        }
    }

    #[test]
    fn test_memory_signed() {
        let mut cpu = Cpu::new(1024, 0);

         let tests = [
            MemReg::U1( i8::max_value() as u8),
            MemReg::U2(i16::max_value() as u16),
            MemReg::U4(i32::max_value() as u32),
            MemReg::U8(i64::max_value() as u64),
            MemReg::U1(0),
            MemReg::U2(0),
            MemReg::U4(0),
            MemReg::U8(0),
            MemReg::U1( i8::min_value() as u8),
            MemReg::U2(i16::min_value() as u16),
            MemReg::U4(i32::min_value() as u32),
            MemReg::U8(i64::min_value() as u64),
        ];

        for &r in tests.iter() {
            cpu.write_memory(r, 0);
            assert_eq!(cpu.read_memory(r.size(), 0), r);
        }
    }
}

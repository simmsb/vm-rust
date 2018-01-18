#[macro_use]
extern crate bitflags;

extern crate byteorder;

use std::ops::Index;
use byteorder::{ByteOrder, NativeEndian};
use std::convert::From;
// use num::Integer

type Reg = u64;

type CpuIndex = u16;

trait CpuIndexable {
    fn register(&self) -> bool;
    fn deref(&self) -> bool;
    fn strip_register(&self) -> Self;
    fn strip_deref(&self) -> Self;
    fn index(&self) -> usize;

    fn make_index(pos: u16, reg: bool, deref: bool) -> Self;
}

impl CpuIndexable for CpuIndex {
    fn register(&self) -> bool {
        self & (1 << 15) != 0
    }

    fn deref(&self) -> bool {
        self & (1 << 14) != 0
    }

    fn strip_register(&self) -> CpuIndex {
        self & !(1 << 15)
    }

    fn strip_deref(&self) -> CpuIndex {
        self & !(1 << 14)
    }

    fn index(&self) -> usize {
        self.strip_register().strip_deref() as usize
    }

    fn make_index(pos: u16, reg: bool, deref: bool) -> CpuIndex {
        pos | (reg as CpuIndex) << 15 | (deref as CpuIndex) << 14
    }
}

struct Cpu {
    mem: Vec<u8>,
    regs: RegBlock,
    flags: CpuFlags,
    cycles: u64,
}

struct RegBlock {
    stk: Reg,
    bas: Reg,
    cur: Reg,
    regs: Vec<Reg>,
}

impl RegBlock {
    fn new(size: usize) -> RegBlock {
        RegBlock {
            stk: 0,
            bas: 0,
            cur: 0,
            regs: vec![0; size],
        }
    }
}

impl Index<usize> for RegBlock {
    type Output = Reg;

    fn index(&self, index: usize) -> &Reg {
        match index {
            0 => &self.stk,
            1 => &self.bas,
            2 => &self.cur,
            x => &self.regs[x],
        }
    }
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

    fn pack(self, val: u64) -> MemReg {
        match self {
            MemSize::U1 => MemReg::U1(val as u8),
            MemSize::U2 => MemReg::U2(val as u16),
            MemSize::U4 => MemReg::U4(val as u32),
            MemSize::U8 => MemReg::U8(val as u64),
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

    fn unpack<N: From<u8> + From<u16> + From<u32> + From<u64>>(self) -> N {
        match self {
            MemReg::U1(x) => N::from(x),
            MemReg::U2(x) => N::from(x),
            MemReg::U4(x) => N::from(x),
            MemReg::U8(x) => N::from(x),
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
            regs: RegBlock::new(regcount),
            flags: CpuFlags::default(),
            cycles: 0,
        }
    }

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

    fn write(&mut self, dat: MemReg, to: CpuIndex) {
        if to.deref() {
            let to = self.read();

            self.write_memory(dat, to);
        } else {
            if to.register() {
                self.regs[to.index()]
            }
            self.write_memory(dat, to.index());
        }
    }

    fn read(&self, size: MemSize, index: CpuIndex) -> MemReg {
        let val = if index.register() {
            self.regs[index.index()] as u64
        } else {
            index.index() as u64
        };

        println!("index: {}", val);

        if index.deref() {
            self.read_memory(size, val as usize)
        } else {
            size.pack(val)
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
            let read = cpu.read_memory(r.size(), 0);
            match (r, read) {
                (MemReg::U1(x), MemReg::U1(y)) => assert_eq!(x as i8, y as i8),
                (MemReg::U2(x), MemReg::U2(y)) => assert_eq!(x as i16, y as i16),
                (MemReg::U4(x), MemReg::U4(y)) => assert_eq!(x as i32, y as i32),
                (MemReg::U8(x), MemReg::U8(y)) => assert_eq!(x as i64, y as i64),
                _ => panic!("Failed to match left and right!"),
            }
        }
    }

    #[test]
    fn test_write_mem() {
        let mut cpu = Cpu::new(1024, 0);
        let val = MemReg::U8(100);
        let mem_index = CpuIndex::make_index(0, false, false);

        cpu.write(val, mem_index.index() as u16);
        assert_eq!(cpu.read_memory(val.size(), mem_index.index()), val);
    }


    #[test]
    fn test_read_mem() {
        let mut cpu = Cpu::new(1024, 0);

        let val = MemReg::U8(100);
        let tests = [
            CpuIndex::make_index(0, false, false),
            CpuIndex::make_index(0, false,  true),
            CpuIndex::make_index(0,  true, false),
            CpuIndex::make_index(0,  true,  true),
        ];

        for &t in tests.iter() {
            cpu.write(val, t.index() as u16);
            assert_eq!(cpu.read(val.size(), t), val);
        }
    }
}


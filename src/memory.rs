use byteorder::{ByteOrder, NativeEndian};
use num::FromPrimitive;

use cpu::{Cpu, CpuIndex, Reg, CpuIndexable};

#[derive(Copy, Clone, FromPrimitive)]
pub enum MemSize {
    U1,
    U2,
    U4,
    U8,
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum MemReg {
    U1(u8),
    U2(u16),
    U4(u32),
    U8(u64),
}

impl MemSize {
    pub fn len(self) -> usize {
        match self {
            MemSize::U1 => 1,
            MemSize::U2 => 2,
            MemSize::U4 => 4,
            MemSize::U8 => 8,
        }
    }

    pub fn pack(self, val: u64) -> MemReg {
        match self {
            MemSize::U1 => MemReg::U1(val as u8),
            MemSize::U2 => MemReg::U2(val as u16),
            MemSize::U4 => MemReg::U4(val as u32),
            MemSize::U8 => MemReg::U8(val as u64),
        }
    }
}

impl MemReg {
    pub fn len(self) -> usize {
        match self {
            MemReg::U1(..) => 1,
            MemReg::U2(..) => 2,
            MemReg::U4(..) => 4,
            MemReg::U8(..) => 8,
        }
    }

    pub fn size(self) -> MemSize {
        match self {
            MemReg::U1(..) => MemSize::U1,
            MemReg::U2(..) => MemSize::U2,
            MemReg::U4(..) => MemSize::U4,
            MemReg::U8(..) => MemSize::U8,
        }
    }

    pub fn unpack<N: FromPrimitive>(self) -> N {
        match self {
            MemReg::U1(x) => N::from_u8(x).unwrap(),
            MemReg::U2(x) => N::from_u16(x).unwrap(),
            MemReg::U4(x) => N::from_u32(x).unwrap(),
            MemReg::U8(x) => N::from_u64(x).unwrap(),
        }
    }

    pub fn unpack_signed<N: FromPrimitive>(self) -> N {
        match self {
            MemReg::U1(x) => N::from_i8(x  as i8).unwrap(),
            MemReg::U2(x) => N::from_i16(x as i16).unwrap(),
            MemReg::U4(x) => N::from_i32(x as i32).unwrap(),
            MemReg::U8(x) => N::from_i64(x as i64).unwrap(),
        }
    }
}


impl Cpu {
    pub fn read_memory(&self, size: MemSize, index: usize) -> MemReg {
        let range = index .. (index + size.len());
        match size {
            MemSize::U1 => MemReg::U1(self.mem[index]),
            MemSize::U2 => MemReg::U2(NativeEndian::read_u16(&self.mem[range])),
            MemSize::U4 => MemReg::U4(NativeEndian::read_u32(&self.mem[range])),
            MemSize::U8 => MemReg::U8(NativeEndian::read_u64(&self.mem[range])),
        }
    }

    pub fn write_memory(&mut self, mem: MemReg, index: usize) {
        let range = index .. (index + mem.len());
        match mem {
            MemReg::U1(x) => self.mem[index] = x,
            MemReg::U2(x) => NativeEndian::write_u16(&mut self.mem[range], x),
            MemReg::U4(x) => NativeEndian::write_u32(&mut self.mem[range], x),
            MemReg::U8(x) => NativeEndian::write_u64(&mut self.mem[range], x),
        }
    }

    pub fn write(&mut self, dat: MemReg, to: CpuIndex) {
        if to.deref() {
            let to = self.read(dat.size(), to.strip_deref()).unpack();
            self.write_memory(dat, to);
        } else {
            if to.register() {
                let val: Reg = dat.unpack();
                self.regs[to.index()] = val;
            } else {
                self.write_memory(dat, to.index());
            }
        }
    }

    pub fn read(&self, size: MemSize, index: CpuIndex) -> MemReg {
        let val = if index.register() {
            self.regs[index.index()] as u64
        } else {
            index.index() as u64
        };

        if index.deref() {
            self.read_memory(size, val as usize)
        } else {
            size.pack(val)
        }
    }
}

use byteorder::{ByteOrder, NativeEndian};

use ::cpu::{Cpu, CpuIndex, Reg, CpuIndexable};

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

    pub fn from_val(val: u8) -> MemSize {
        match val {
            0 => MemSize::U1,
            1 => MemSize::U2,
            2 => MemSize::U4,
            3 => MemSize::U8,
            _ => panic!("failed to decode size: {}", val),
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

    pub fn unpack(self) -> u64 {
        match self {
            MemReg::U1(x) => x as u64,
            MemReg::U2(x) => x as u64,
            MemReg::U4(x) => x as u64,
            MemReg::U8(x) => x as u64,
        }
    }

    pub fn unpack_signed(self) -> i64 {
        match self {
            MemReg::U1(x) => x as i8  as i64,
            MemReg::U2(x) => x as i16 as i64,
            MemReg::U4(x) => x as i32 as i64,
            MemReg::U8(x) => x as i64,
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
        // println!("Writing {:?} to index: {}", mem, index);
        let range = index .. (index + mem.len());
        match mem {
            MemReg::U1(x) => self.mem[index] = x,
            MemReg::U2(x) => NativeEndian::write_u16(&mut self.mem[range], x),
            MemReg::U4(x) => NativeEndian::write_u32(&mut self.mem[range], x),
            MemReg::U8(x) => NativeEndian::write_u64(&mut self.mem[range], x),
        }

        // let readback = self.read_memory(mem.size(), index);
        // println!("Wrote {:?} to {} and read back {:?}", mem, index, readback);
    }

    pub fn write(&mut self, dat: MemReg, to: CpuIndex) {
        if to.register() {
            if to.deref() {
                let location = self.regs[to.index()];
                self.write_memory(dat, location as usize);
            } else {
                self.regs[to.index()] = dat.unpack();
            }
        } else {
            if to.deref() {
                self.write_memory(dat, to.index());
            } else {
                panic!("Cannot write to literal! {}, CPU: {:?}", to.debug(), self);
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

    pub fn push(&mut self, mem: MemReg) {
        let stkpos = self.regs.stk as usize;
        self.write_memory(mem, stkpos);
        self.regs.stk += mem.len() as u64;
    }

    pub fn pop(&mut self, size: MemSize) -> MemReg {
        self.regs.stk -= size.len() as u64;
        self.read_memory(size, self.regs.stk as usize)
    }
}

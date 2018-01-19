use std::ops::{Index, IndexMut};


pub type Reg = u64;

pub type CpuIndex = u16;

pub trait CpuIndexable {
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

pub struct Cpu {
    pub mem: Vec<u8>,
    pub regs: RegBlock,
    pub flags: CpuFlags,
    pub cycles: u64,
}

impl Cpu {
    pub fn new(memsize: usize, regcount: usize) -> Cpu {
        Cpu {
            mem: vec![0; memsize],
            regs: RegBlock::new(regcount),
            flags: CpuFlags::default(),
            cycles: 0,
        }
    }
}

pub struct RegBlock {
    pub stk: Reg,
    pub bas: Reg,
    pub cur: Reg,
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

impl IndexMut<usize> for RegBlock {
    fn index_mut(&mut self, index: usize) -> &mut Reg {
        match index {
            0 => &mut self.stk,
            1 => &mut self.bas,
            2 => &mut self.cur,
            x => &mut self.regs[x],
        }
    }
}

bitflags! {
    #[derive(Default)]
    pub struct CpuFlags: u8 {
        const RUNNING = 0b0000001;
        const SIGNED  = 0b0000010;
        const ZERO    = 0b0000100;
        const LE      = 0b0001000;
    }
}
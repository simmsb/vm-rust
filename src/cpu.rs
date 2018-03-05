use std::fs::File;
use std::io::Read;
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
    pub running: bool,
}

impl Cpu {
    pub fn new(memsize: usize, regcount: usize) -> Cpu {
        Cpu {
            mem: vec![0; memsize],
            regs: RegBlock::new(regcount),
            flags: CpuFlags::default(),
            cycles: 0,
            running: true,
        }
    }

    pub fn exe_loop(&mut self) {
        while self.running {
            let instr = self.get_instr();
            self.run_instr(instr);
        }
    }

    pub fn load_file(&mut self, filename: &str) {
        let mut file = File::open(filename).unwrap();
        file.read_to_end(&mut self.mem).unwrap();
    }
}

#[derive(Debug)]
pub struct RegBlock {
    pub stk: Reg,
    pub bas: Reg,
    pub cur: Reg,
    pub ret: Reg,
    regs: Vec<Reg>,
}

impl RegBlock {
    fn new(size: usize) -> RegBlock {
        RegBlock {
            stk: 0,
            bas: 0,
            cur: 0,
            ret: 0,
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
            3 => &self.ret,
            x => &self.regs[x - 4],
        }
    }
}

impl IndexMut<usize> for RegBlock {
    fn index_mut(&mut self, index: usize) -> &mut Reg {
        match index {
            0 => &mut self.stk,
            1 => &mut self.bas,
            2 => &mut self.cur,
            3 => &mut self.ret,
            x => &mut self.regs[x - 4],
        }
    }
}

bitflags! {
    #[derive(Default)]
    pub struct CpuFlags: u8 {
        const EQ      = 0b0000001;
        const LE      = 0b0000010;  // unsigned le
        const LS      = 0b0000100;  // signed le
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regblock() {
        let reg_count = 10;
        let mut block = RegBlock::new(reg_count - 3);

        block.stk = 1;
        assert_eq!(block.stk, 1);
        assert_eq!(block[0], 1);
        block[1] = 2;
        assert_eq!(block.bas, 2);
        for i in 0..10 {
            block[i] = i as u64;
            assert_eq!(block[i], i as u64);
        }
    }
}

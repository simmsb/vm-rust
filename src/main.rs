extern crate num;

use std::mem;
use std::ops::{Shl, BitOr};
use num::{PrimInt, Unsigned};
use num::cast::NumCast;

#[macro_use]
extern crate bitflags;

type Reg = u64;

struct Cpu {
    mem: Vec<u8>,
    regs: Vec<Reg>,
    flags: CpuFlags,
    cycles: u64,
}

enum MemSize {
    U1,
    U2,
    U4,
    U8,
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
            mem: Vec::with_capacity(memsize),
            regs: Vec::with_capacity(regcount),
            flags: CpuFlags::default(),
            cycles: 0,
        }
    }
}

fn read_size<N: Shl<R> + PrimInt + Unsigned, R: PrimInt + Unsigned + BitOr>(mem: &[N]) -> R {
    mem.iter().enumerate().fold(R::zero(), | sum, (index , &val) | {
        sum | NumCast::from(val << ((mem.len() - index) * mem::size_of::<N>())).unwrap()
    })
}

impl Cpu {
    fn read_memory(&mut self, size: MemSize, index: usize) -> Reg {
        read_size(&self.mem[index..(index + size.len())])
    }
}

fn main() {
    let mut cpu = Cpu::new(1 << 16, 8);

    let mematzero = cpu.read_memory(MemSize::U8, 0);
    println!("memory is: {}", mematzero);
}

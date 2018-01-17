extern crate num;

use std::mem;
use std::ops::Shl;
use num::PrimInt;

#[macro_use]
extern crate bitflags;

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
            mem: vec![0; memsize],
            regs: vec![0; regcount],
            flags: CpuFlags::default(),
            cycles: 0,
        }
    }
}

fn unpack_size<N: Shl<R> + PrimInt, R: PrimInt>(mem: &[N]) -> R {
    mem.iter().enumerate().fold(R::zero(), | sum, (index , &val) | {
        let shift = index * mem::size_of::<N>() * 8;
        let base: R = num::cast(val).unwrap();
        sum | (base << shift)
    })
}

impl Cpu {
    fn read_memory(& self, size: MemSize, index: usize) -> Reg {
        let range = index .. (index + size.len());
        unpack_size(&self.mem[range])
    }

    fn write_memory(&mut self, size: MemSize, index: usize, value: u64) {
        self.mem[index .. (index + size.len())]
            .iter_mut().enumerate()
            .for_each(| (index, val) | {
                let shift = index * 8;
                let dat = ((value >> shift) & 0xff) as u8;
                *val = dat;
            });
    }
}

fn main() {
    let mut cpu = Cpu::new(1 << 16, 8);

    cpu.write_memory(MemSize::U4, 0, 0xffffffff);

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
            (MemSize::U1,  u8::max_value() as u64),
            (MemSize::U2, u16::max_value() as u64),
            (MemSize::U4, u32::max_value() as u64),
            (MemSize::U8, u64::max_value() as u64),
            (MemSize::U1, 0),
            (MemSize::U2, 0),
            (MemSize::U4, 0),
            (MemSize::U8, 0),
        ];

        for &(size, num) in tests.iter() {
            cpu.write_memory(size, 0, num);
            assert_eq!(cpu.read_memory(size, 0), num);
        }
    }

    #[test]
    fn test_memory_signed() {
        let mut cpu = Cpu::new(1024, 0);

        let tests = [
            (MemSize::U1,  i8::max_value() as i64),
            (MemSize::U2, i16::max_value() as i64),
            (MemSize::U4, i32::max_value() as i64),
            (MemSize::U8, i64::max_value() as i64),
            (MemSize::U1, 0),
            (MemSize::U2, 0),
            (MemSize::U4, 0),
            (MemSize::U8, 0),
        ];

        for &(size, num) in tests.iter() {
            cpu.write_memory(size, 0, num as u64);
            assert_eq!(cpu.read_memory(size, 0) as i64, num);
        }
    }
}

use num::FromPrimitive;

use cpu::{Cpu, Reg};
use memory::{MemReg, MemSize};

//  size  type     id
//  [bb][bbbbbb][bbbbbbb]
//
//  type is Binary, Unary, Manip, etc
//  id is individual id, Add, Sub, etc
//

type InstrNum = u16;

trait InstrDecode {
    fn size(&self) -> u8;
    fn ityp(&self) -> u8;
    fn id  (&self) -> u8;
}

impl InstrDecode for InstrNum {
    fn size(&self) -> u8 { (self >> 14) as u8 }
    fn ityp(&self) -> u8 { (self >> 8)  as u8 }
    fn id  (&self) -> u8 { *self         as u8 }
}

mod instr_intern_types {
    pub enum Bin {
        Add,
        Sub,
        Mul,
        UDiv,
        IDiv,
        Shl,
        Shr,
        Sar,
        And,
        Or,
        Xor,
    }

    pub enum Un {
        Neg,
        Pos,
        Not,
    }

    pub enum CpuManip {
        Mov,
        Sxu,
        Sxi,
        Jmp,
        Tst,
        Halt,
    }

    pub enum MemManip {
        Stks,
        Push,
        Pop,
        Call,
        Ret,
    }

    pub enum CpuIO {
        Getc,
        Putc,
    }
}

use self::instr_intern_types::*;

pub enum InstrType {
    Binary(Bin),
    Unary(Un),
    Manip(CpuManip),
    Mem(MemManip),
    IO(CpuIO),
}

impl InstrType {

    fn decode(val: InstrNum) -> Self {
        use InstrType::*;

        match val.ityp() {
            0 => Binary(match val.id() {
                0  => Bin::Add,
                1  => Bin::Sub,
                2  => Bin::Mul,
                3  => Bin::UDiv,
                4  => Bin::IDiv,
                5  => Bin::Shl,
                6  => Bin::Shr,
                7  => Bin::Sar,
                8  => Bin::And,
                9  => Bin::Or,
                10 => Bin::Xor,
                _ => panic!("Invalid Binary instruction type."),
            }),
            1 => Unary(match val.id() {
                0 => Un::Neg,
                1 => Un::Pos,
                2 => Un::Not,
                _ => panic!("Invalid Unary instruction type."),
            }),
            2 => Manip(match val.id() {
                0 => CpuManip::Mov,
                1 => CpuManip::Sxu,
                2 => CpuManip::Sxi,
                3 => CpuManip::Jmp,
                4 => CpuManip::Tst,
                5 => CpuManip::Halt,
                _ => panic!("Invalid Manipulation instruction type."),
            }),
            3 => Mem(match val.id() {
                0 => MemManip::Stks,
                1 => MemManip::Push,
                2 => MemManip::Pop,
                3 => MemManip::Call,
                4 => MemManip::Ret,
                _ => panic!("Invalid Memory instruction type."),
            }),
            4 => IO(match val.id() {
                0 => CpuIO::Getc,
                1 => CpuIO::Putc,
                _ => panic!("Invalid IO instruction type."),
            }),
            _ => panic!("Could not decode instruction"),
        }
    }
}

pub struct Instruction {
    instr: InstrType,
    size: MemSize,
}

impl Cpu {
    fn get_next(&mut self, size: MemSize) -> MemReg {
        let val = self.read_memory(size, self.regs.cur as usize);
        self.regs.cur += size.len() as Reg;
        val
    }

    pub fn get_instr(&mut self) -> Instruction {
        let val: InstrNum = self.get_next(MemSize::U2).unpack();

        Instruction {
            instr: InstrType::decode(val),
            size: FromPrimitive::from_u8(val.size()).unwrap(),
        }
    }

    pub fn run_instr(&mut self, instr: Instruction) {
        use InstrType::*;

        match instr.instr {
            Binary(x) => {
                use self::Bin::*;

                let (left, right) = (self.get_next(MemSize::U2).unpack(),
                                     self.get_next(MemSize::U2).unpack());
                let to = self.get_next(MemSize::U2).unpack();

                let (lhs, rhs) : (u64, u64) = (self.read(instr.size, left).unpack(),
                                               self.read(instr.size, right).unpack());

                // TODO: might have to do instr.size.operator(lhs, rhs, | x, y | { x + y })
                // if this doesn't work
                let result = match x {
                    Add  => lhs + rhs,
                    Sub  => lhs - rhs,
                    Mul  => lhs * rhs,
                    UDiv => lhs / rhs,
                    IDiv => ((lhs as i64) / (rhs as i64)) as u64,
                    Shl  => lhs << rhs,
                    Shr  => lhs >> rhs,
                    Sar  => ((lhs as i64) >> rhs) as u64,
                    And  => lhs & rhs,
                    Or   => lhs | rhs,
                    Xor  => lhs ^ rhs,
                };
                self.write(instr.size.pack(result), to);
            },
            Unary(x) => {
                use self::Un::*;

                let op = self.get_next(MemSize::U2).unpack();
                let to = self.get_next(MemSize::U2).unpack();

                let val: u64 = self.read(instr.size, op).unpack();

                let result = match x {
                    Neg => -(val as i64) as u64,
                    Pos => (val as i64).abs() as u64,
                    Not => !val,
                };
                self.write(instr.size.pack(result), to);
            },
            Manip(x) => {
                use self::CpuManip::*;

                match x {
                    Mov => {
                        let from = self.get_next(MemSize::U2).unpack();
                        let to = self.get_next(MemSize::U2).unpack();

                        let val = self.read(instr.size, from);
                        self.write(val, to);
                    },
                    _   => panic!("unfinished instructions"),
                };
            },
            _ => panic!("unfinished instructions"),
        }
    }
}
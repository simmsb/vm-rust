use std::fmt;
use std::io::{self, Read, Write};
use num::FromPrimitive;
use std::num::Wrapping;

#[allow(unused_imports)]
use ::cpu::{Cpu, Reg, CpuFlags, CpuIndex, CpuIndexable};
use ::memory::{MemReg, MemSize};

//  size  type     id
//  [bb][bbbbbb][bbbbbbbb]
//
//  type is Binary, Unary, Manip, etc
//  id is individual id, Add, Sub, etc
//

#[derive(Copy, Clone)]
pub struct InstrNum(pub u16);

trait InstrDecode {
    fn size(&self) -> u8;
    fn ityp(&self) -> u8;
    fn id  (&self) -> u8;
}

trait InstrEncode {
    fn encode(&self, size: u8) -> InstrNum;
}

impl InstrDecode for InstrNum {
    fn size(&self) -> u8 { (self.0 >> 14)         as u8 }
    fn ityp(&self) -> u8 { ((self.0 >> 8) & 0x3f) as u8 }
    fn id  (&self) -> u8 {  self.0                as u8 }
}

impl fmt::Debug for InstrNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Instruction {{ size: {}, ityp: {}, id: {} }}", self.size(), self.ityp(), self.id())
    }
}

#[derive(Copy, Clone, Debug)]
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

impl InstrEncode for Bin {
    #[allow(dead_code)]
    fn encode(&self, size: u8) -> InstrNum {
        return InstrNum((size as u16) << 14 | *self as u16);
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Un {
    Neg,
    Pos,
    Not,
}

impl InstrEncode for Un {
    #[allow(dead_code)]
    fn encode(&self, size: u8) -> InstrNum {
        return InstrNum((size as u16) << 14 | 1 << 8 | *self as u16);
    }
}

#[derive(Copy, Clone, Debug)]
pub enum CpuManip {
    Mov,
    Sxu,
    Sxi,
    Jmp,
    Set,
    Tst,
    Halt,
}

impl InstrEncode for CpuManip {
    #[allow(dead_code)]
    fn encode(&self, size: u8) -> InstrNum {
        return InstrNum((size as u16) << 14 | 2 << 8 | *self as u16);
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MemManip {
    Stks,
    Push,
    Pop,
    Call,
    Ret,
}

impl InstrEncode for MemManip {
    #[allow(dead_code)]
    fn encode(&self, size: u8) -> InstrNum {
        return InstrNum((size as u16) << 14 | 3 << 8 | *self as u16);
    }
}

#[derive(Copy, Clone, Debug)]
pub enum CpuIO {
    Getc,
    Putc,
}

impl InstrEncode for CpuIO {
    #[allow(dead_code)]
    fn encode(&self, size: u8) -> InstrNum {
        return InstrNum((size as u16) << 14 | 4 << 8 | *self as u16);
    }
}


#[derive(Copy, Clone)]
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
                4 => CpuManip::Set,
                5 => CpuManip::Tst,
                6 => CpuManip::Halt,
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
            _ => panic!("Could not decode instruction {:?}", val),
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

    fn read_next(&mut self, size: MemSize) -> MemReg {
        let val = self.get_next(MemSize::U2).unpack();
        self.read(size, val as u16)
    }

    pub fn get_instr(&mut self) -> Instruction {
        let val = InstrNum(self.get_next(MemSize::U2).unpack() as u16);

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

                let (left, right) = (self.read_next(instr.size),
                                     self.read_next(instr.size));
                let to = self.get_next(MemSize::U2).unpack() as u16;

                let (lhs, rhs) = (Wrapping(left.unpack()), Wrapping(right.unpack()));

                // TODO: might have to do instr.size.operator(lhs, rhs, | x, y | { x + y })
                // if this doesn't work
                let result = match x {
                    Add  => lhs + rhs,
                    Sub  => lhs - rhs,
                    Mul  => lhs * rhs,
                    UDiv => lhs / rhs,
                    IDiv => {
                        let (lhs, rhs) = (Wrapping(left.unpack_signed()), Wrapping(right.unpack_signed()));
                        Wrapping((lhs / rhs).0 as u64)
                    },
                    Shl  => lhs << rhs.0 as usize,
                    Shr  => lhs >> rhs.0 as usize,
                    Sar  => {
                        let lhs: i64 = left.unpack_signed();
                        Wrapping((lhs >> rhs.0) as u64)
                    },
                    And  => lhs & rhs,
                    Or   => lhs | rhs,
                    Xor  => lhs ^ rhs,
                };
                self.write(instr.size.pack(result.0), to);
            },
            Unary(x) => {
                use self::Un::*;

                let op   = self.get_next(MemSize::U2).unpack() as u16;
                let op_u: u64 = self.read(instr.size, op).unpack();
                let op_s: i64 = self.read(instr.size, op).unpack_signed();
                let to = self.get_next(MemSize::U2).unpack() as u16;

                let result = match x {
                    Neg => -op_s as u64,
                    Pos => op_s.abs() as u64,
                    Not => !op_u,
                };
                self.write(instr.size.pack(result), to);
            },
            Manip(x) => {
                use self::CpuManip::*;

                match x {
                    Mov => {
                        let from = self.read_next(instr.size);
                        let to   = self.get_next(MemSize::U2).unpack() as u16;

                        self.write(from, to);
                    },
                    Sxu => {
                        let from = self.read_next(instr.size).unpack();
                        let size = self.get_next(MemSize::U1).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;
                        println!("to = {}", to);
                        let result = match size {
                            0 => MemReg::U1(from as u8),
                            1 => MemReg::U2(from as u16),
                            2 => MemReg::U4(from as u32),
                            3 => MemReg::U8(from as u64),
                            _ => panic!("Invalid size to Sxu"),
                        };
                        self.write(result, to);
                    },
                    Sxi => {
                        let from = self.get_next(MemSize::U2).unpack() as u16;
                        let size = self.get_next(MemSize::U1).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;

                        println!("to = {}", to);
                        let val = self.read(instr.size, from).unpack_signed();
                        let result = match size {
                            0 => MemReg::U1(val as i8 as u8),
                            1 => MemReg::U2(val as i16 as u16),
                            2 => MemReg::U4(val as i32 as u32),
                            3 => MemReg::U8(val as i64 as u64),
                            _ => panic!("Invalid size to Sxi"),
                        };
                        self.write(result, to);
                    },
                    Jmp => {
                        let check = self.read_next(MemSize::U1).unpack() as u8;
                        let loc   = self.read_next(instr.size).unpack();
                        if check != 0 {
                            self.regs.cur = loc;
                        };
                    },
                    Set => {
                        let cond = self.get_next(MemSize::U1).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;
                        let check = match cond {
                            0 => true,
                            1 => self.flags.contains(CpuFlags::LE),
                            2 => self.flags.intersects(CpuFlags::LE | CpuFlags::EQ),
                            3 => self.flags.contains(CpuFlags::EQ),
                            4 => !self.flags.contains(CpuFlags::EQ),
                            5 => !self.flags.contains(CpuFlags::LE | CpuFlags::EQ),
                            6 => !self.flags.contains(CpuFlags::LE),
                            _ => panic!("invalid condition to Jmp instruction."),
                        };

                        self.write(MemReg::U1(check as u8), to);
                    }
                    Tst => {
                        let lhs = self.read_next(instr.size);
                        let rhs = self.read_next(instr.size);

                        let (lhs_u, rhs_u): (u64, u64) = (lhs.unpack(), rhs.unpack());
                        let (lhs_s, rhs_s): (i64, i64) = (lhs.unpack_signed(), rhs.unpack_signed());

                        self.flags.set(CpuFlags::EQ, lhs_u == rhs_u);
                        self.flags.set(CpuFlags::LE, lhs_u <  rhs_u);
                        self.flags.set(CpuFlags::LS, lhs_s <  rhs_s);
                    },
                    Halt => {
                        self.running = false;
                    },
                };
            },
            Mem(x) => {
                use self::MemManip::*;

                match x {
                    Stks => {
                        let pos = self.read_next(instr.size).unpack();
                        self.regs.stk = pos;
                    },
                    Push => {
                        let data = self.read_next(instr.size);
                        self.push(data);
                    },
                    Pop => {
                        let to  = self.get_next(MemSize::U2).unpack() as u16;
                        let val = self.pop(instr.size);
                        self.write(val, to);
                    },
                    Call => {
                        let jmp_pos = self.read_next(instr.size).unpack();
                        let cur = MemReg::U2(self.regs.cur as u16 + 1);
                        self.push(cur);  // return address
                        self.regs.cur = jmp_pos;

                        let baseptr = MemReg::U8(self.regs.bas);
                        self.push(baseptr); // save base pointer
                        self.regs.bas = self.regs.stk;
                    },
                    Ret => {
                        //  | p1 | p2 | return_address | saved_base_pointer | local ...
                        //                    ^(2)               ^(1)
                        //  Stack will look like this when Ret is called
                        //  first make stack pointer point to the saved base pointer (1)
                        //  pop base pointer, stack now points to return address (2)
                        //  pop return address, then restore base pointer to the saved base pointer
                        //  decrement stack pointer by param to ret to clear locals
                        //  jump to return address
                        let param_len: u64 = self.read_next(instr.size).unpack();
                        self.regs.stk   = self.regs.bas;
                        let baseptr     = self.pop(MemSize::U8).unpack();
                        let return_addr = self.pop(MemSize::U2).unpack();
                        self.regs.bas   = baseptr;
                        self.regs.stk  -= param_len;
                        self.regs.cur   = return_addr;
                    },
                };
            },
            IO(x) => {
                use self::CpuIO::*;

                match x {
                    Getc => {
                        let to = self.get_next(MemSize::U2).unpack() as u16;
                        let mut arr = [0];
                        io::stdin().read_exact(&mut arr).unwrap();
                        self.write(MemReg::U1(arr[0]), to);
                    },
                    Putc => {
                        let val = [self.read_next(instr.size).unpack() as u8];
                        io::stdout().write(&val).unwrap();
                    }
                }
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    const SIZES : [MemSize; 4] = [MemSize::U1, MemSize::U2, MemSize::U4, MemSize::U8];

    fn push_args(cpu: &mut Cpu, args: &[MemReg]) -> Vec<u16> {
        cpu.regs.stk = 0;
        args.into_iter().map(| &arg | {
            let pos = cpu.regs.stk;
            cpu.push(arg);
            pos as u16
        }).collect()
    }

    fn make_memrefs(indexes: &Vec<u16>) -> Vec<MemReg> {
        indexes.into_iter().map(| &index | {
            MemReg::U2(CpuIndex::make_index(index, false, true))
        }).collect()
    }

    fn build_instruction<T: InstrEncode>(cpu: &mut Cpu, instr: T, size: MemSize, params: &[MemReg]) -> MemReg {
        let result_place = CpuIndex::make_index(3, true, false);
        cpu.regs.cur = cpu.regs.stk;
        cpu.push(MemReg::U2(instr.encode(size as u8).0));
        for &param in params {
            cpu.push(param);
        }
        cpu.push(MemReg::U2(result_place));

        cpu.write(size.pack(0), result_place);

        let instr = cpu.get_instr();
        cpu.run_instr(instr);

        cpu.read(size, result_place)
    }

    #[test]
    fn test_binary_ops() {
        use instruction::Bin::*;

        let mut cpu = Cpu::new(100, 10);

        let ta: u64 = 4;
        let tb: u64 = 2;

        let tests = [
            (Add,  ta + tb),
            (Sub,  ta - tb),
            (Mul,  ta * tb),
            (UDiv, ta / tb),
            (Shl, ta << tb),
            (Shr, ta >> tb),
            (And, ta & tb),
            (Or,  ta | tb),
            (Xor, ta ^ tb),
        ];

        let ta_s: i64 = -8;

        let stests = [
            (IDiv, ta_s /  tb as i64),
            (Sar,  ta_s >> tb),
        ];

        for &size in SIZES.iter() {
            for &(op, expected) in tests.iter() {
                let indexes = push_args(&mut cpu, &[size.pack(ta), size.pack(tb)]);
                let params  = make_memrefs(&indexes);
                let result  = build_instruction(&mut cpu, op, size, &params);
                assert_eq!(result, size.pack(expected), "instruction: {:?}", op);
            }

            for &(op, expected) in stests.iter() {
                let indexes = push_args(&mut cpu, &[size.pack(ta_s as u64), size.pack(tb)]);
                let params  = make_memrefs(&indexes);
                let result  = build_instruction(&mut cpu, op, size, &params).unpack_signed();
                assert_eq!(result, expected, "instruction: {:?}", op);
            }
        }
    }

    #[test]
    fn test_unary_ops() {
        use instruction::Un::*;

        let mut cpu = Cpu::new(100, 10);
        let t: i64 = -5;

        let tests = [
            (Neg, -t),
            (Pos, t.abs()),
            (Not, !t),
        ];

        for &size in SIZES.iter() {
            for &(op, expected) in tests.iter() {
                let indexes = push_args(&mut cpu, &[size.pack(t as u64)]);
                let params  = make_memrefs(&indexes);
                let result  = build_instruction(&mut cpu, op, size, &params).unpack_signed();
                assert_eq!(result, expected, "instruction: {:?}", op);
            }
        }
    }

    #[test]
    fn test_cpu_manip_mov() {
        use instruction::CpuManip::Mov;

        let mut cpu = Cpu::new(100, 10);

        let test_num = 0x5a5a5a5a;

        for &size in SIZES.iter() {
            let indexes = push_args(&mut cpu, &[size.pack(test_num)]);
            let params  = make_memrefs(&indexes);
            let result  = build_instruction(&mut cpu, Mov, size, &params);
            assert_eq!(result, size.pack(test_num), "instruction: {:?}", Mov);
        }
    }

    #[test]
    fn test_cpu_manip_sxu_sxi() {
        use instruction::CpuManip::{Sxi, Sxu};

        let mut cpu = Cpu::new(100, 10);

        let  sign_num: i8 = -12;
        let usign_num: u8 =  12;

        for &size in SIZES.iter() {
            let indexes = push_args(&mut cpu, &[size.pack(sign_num as u8 as u64)]);
            let mut params  = make_memrefs(&indexes);
            params.push(MemReg::U1(0));
            let signed_result = build_instruction(&mut cpu, Sxi, size, &params).unpack_signed() as i8;

            let indexes = push_args(&mut cpu, &[size.pack(usign_num as u64)]);
            let mut params  = make_memrefs(&indexes);
            params.push(MemReg::U1(0));
            let unsign_result = build_instruction(&mut cpu, Sxu, size, &params).unpack() as u8;

            assert_eq!(signed_result,  sign_num);
            assert_eq!(unsign_result, usign_num);
        }
    }
}

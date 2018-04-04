use std::{
    fmt,
    io::{self, Read, Write},
    num::Wrapping,
    marker::Sized,
    convert::From,
};

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
    #[inline]
    fn group_index() -> u16;

    #[inline]
    fn instr_index(&self) -> u16;

    fn encode(&self, size: u8) -> InstrNum {
        InstrNum((size as u16) << 14 | Self::group_index() << 8 | self.instr_index())
    }
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
    IMod,
    UMod,
}

impl InstrEncode for Bin {
    fn group_index() -> u16 { 0 }

    fn instr_index(&self) -> u16 { *self as u16 }
}

#[derive(Copy, Clone, Debug)]
pub enum Un {
    Binv,
    Linv,
    Neg,
    Pos,
}

impl InstrEncode for Un {
    fn group_index() -> u16 { 1 }

    fn instr_index(&self) -> u16 { *self as u16 }
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
    fn group_index() -> u16 { 2 }

    fn instr_index(&self) -> u16 { *self as u16 }
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
    fn group_index() -> u16 { 3 }

    fn instr_index(&self) -> u16 { *self as u16 }
}

#[derive(Copy, Clone, Debug)]
pub enum CpuIO {
    Getc,
    Putc,
    PutInt,
}

impl InstrEncode for CpuIO {
    fn group_index() -> u16 { 4 }

    fn instr_index(&self) -> u16 { *self as u16 }
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
                11 => Bin::IMod,
                12 => Bin::UMod,
                _ => panic!("Invalid Binary instruction type: {}.", val.id()),
            }),
            1 => Unary(match val.id() {
                0 => Un::Binv,
                1 => Un::Linv,
                2 => Un::Neg,
                3 => Un::Pos,
                _ => panic!("Invalid Unary instruction type: {}.", val.id()),
            }),
            2 => Manip(match val.id() {
                0 => CpuManip::Mov,
                1 => CpuManip::Sxu,
                2 => CpuManip::Sxi,
                3 => CpuManip::Jmp,
                4 => CpuManip::Set,
                5 => CpuManip::Tst,
                6 => CpuManip::Halt,
                _ => panic!("Invalid Manipulation instruction type: {}.", val.id()),
            }),
            3 => Mem(match val.id() {
                0 => MemManip::Stks,
                1 => MemManip::Push,
                2 => MemManip::Pop,
                3 => MemManip::Call,
                4 => MemManip::Ret,
                _ => panic!("Invalid Memory instruction type: {}.", val.id()),
            }),
            4 => IO(match val.id() {
                0 => CpuIO::Getc,
                1 => CpuIO::Putc,
                2 => CpuIO::PutInt,
                _ => panic!("Invalid IO instruction type: {}.", val.id()),
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
            size: MemSize::from_val(val.size()),
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
                    IMod => {
                        let (lhs, rhs) = (Wrapping(left.unpack_signed()), Wrapping(right.unpack_signed()));
                        Wrapping((lhs % rhs).0 as u64)
                    },
                    UMod => lhs % rhs,
                };
                self.write(instr.size.pack(result.0), to);
            },
            Unary(x) => {
                use self::Un::*;

                let op   = self.get_next(MemSize::U2).unpack() as u16;
                let op_u: u64 = self.read(instr.size, op).unpack();
                let op_s: i64 = self.read(instr.size, op).unpack_signed();
                let to = self.get_next(MemSize::U2).unpack() as u16;
                // (binv, linv, neg, pos) = range(4)
                let result = match x {
                    Binv => !op_u,
                    Linv => (op_u == 0) as u64,
                    Neg => -op_s as u64,
                    Pos => op_s.abs() as u64,
                };
                self.write(instr.size.pack(result), to);
            },
            Manip(x) => {
                use self::CpuManip::*;

                match x {
                    Mov => {
                        let to   = self.get_next(MemSize::U2).unpack() as u16;
                        let from = self.read_next(instr.size);

                        // if (to as CpuIndex).deref() {
                        //     println!("writing {:?} to {:?}", from, (to as CpuIndex).debug());
                        // }

                        self.write(from, to);
                    },
                    Sxu => {
                        let from = self.read_next(instr.size).unpack();
                        let size = self.get_next(MemSize::U2).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;
                        let result = match size {
                            0 => MemReg::U1(from as u8),
                            1 => MemReg::U2(from as u16),
                            2 => MemReg::U4(from as u32),
                            3 => MemReg::U8(from as u64),
                            _ => panic!("Invalid size to Sxu: {}", size),
                        };
                        self.write(result, to);
                    },
                    Sxi => {
                        let from = self.get_next(MemSize::U2).unpack() as u16;
                        let size = self.get_next(MemSize::U2).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;

                        let val = self.read(instr.size, from).unpack_signed();
                        let result = match size {
                            0 => MemReg::U1(val as i8 as u8),
                            1 => MemReg::U2(val as i16 as u16),
                            2 => MemReg::U4(val as i32 as u32),
                            3 => MemReg::U8(val as i64 as u64),
                            _ => panic!("Invalid size to Sxi: {}", size),
                        };
                        self.write(result, to);
                    },
                    Jmp => {
                        let check = self.read_next(instr.size).unpack() as u8;
                        let loc   = self.read_next(MemSize::U2).unpack();
                        if check != 0 {
                            self.regs.cur = loc;
                        };
                    },
                    Set => {
                        let cond = self.get_next(MemSize::U2).unpack();
                        let to   = self.get_next(MemSize::U2).unpack() as u16;
                        let check = match cond {
                            0 => true,
                            1 => self.flags.contains(CpuFlags::LE),
                            2 => self.flags.intersects(CpuFlags::LE | CpuFlags::EQ),
                            3 => self.flags.contains(CpuFlags::EQ),
                            4 => self.flags.contains(CpuFlags::LS),
                            5 => self.flags.intersects(CpuFlags::LS | CpuFlags::EQ),
                            6 => !self.flags.contains(CpuFlags::LE),
                            7 => !self.flags.contains(CpuFlags::LE | CpuFlags::EQ),
                            8 => !self.flags.contains(CpuFlags::EQ),
                            9 => !self.flags.contains(CpuFlags::LS),
                            10 => !self.flags.intersects(CpuFlags::LS | CpuFlags::EQ),
                            _ => panic!("invalid condition to Jmp instruction."),
                        };

                        if cfg!(feature = "debug_flag") {
                            println!("setting {:?} on condition {}, result was: {}", to, cond, check);
                        }

                        self.write(instr.size.pack(check as u64), to);
                    }
                    Tst => {
                        let lhs = self.read_next(instr.size);
                        let rhs = self.read_next(instr.size);

                        let (lhs_u, rhs_u): (u64, u64) = (lhs.unpack(), rhs.unpack());
                        let (lhs_s, rhs_s): (i64, i64) = (lhs.unpack_signed(), rhs.unpack_signed());

                        if cfg!(feature = "debug_flag") {
                            println!("Testing {} with {}", lhs_u, rhs_u);
                        }

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
                        let cur = MemReg::U2(self.regs.cur as u16);
                        self.push(cur);  // return address
                        self.regs.cur = jmp_pos;

                        let baseptr = MemReg::U2(self.regs.bas as u16);
                        self.push(baseptr); // save base pointer
                        self.regs.bas = self.regs.stk;
                    },
                    Ret => {
                        //  | p1 | p2 | return_address | saved_base_pointer | local ...
                        //                    ^(2)               ^(1)            ^(base pointer and stack pointer)
                        //  Stack will look like this when Ret is called,
                        //  with the stack and base pointer both pointing to just after the saved base pointer
                        //  pop base pointer, stack now points to return address (2)
                        //  pop return address, then restore base pointer to the saved base pointer
                        //  jump to return address
                        self.regs.stk   = self.regs.bas;  // stack pointer points to base pointer
                        let baseptr     = self.pop(MemSize::U2).unpack();  // pop off saved base pointer
                        let return_addr = self.pop(MemSize::U2).unpack();  // pop off return address
                        self.regs.bas   = baseptr;  // restore previous base pointer
                        self.regs.cur   = return_addr;  // jump to return address
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
                    },
                    PutInt => {
                        let val = self.read_next(instr.size).unpack();
                        println!("{}", val);
                    }
                }
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    // use test::Bencher;

    const SIZES : [MemSize; 4] = [MemSize::U1, MemSize::U2, MemSize::U4, MemSize::U8];

    fn push_args(cpu: &mut Cpu, args: &[MemReg]) -> (Vec<u16>, usize) {
        let mut base = 0;
        let indexes = args.into_iter().map(| &arg | {
            let pos = base;
            cpu.write_memory(arg, base);
            base += arg.len();
            pos as u16
        }).collect();
        (indexes, base)
    }

    fn make_memrefs(indexes: &Vec<u16>) -> Vec<MemReg> {
        indexes.into_iter().map(| &index | {
            MemReg::U2(CpuIndex::make_index(index, false, true))
        }).collect()
    }

    fn write_instruction(cpu: &mut Cpu, base: usize, instr: MemReg, params: &[MemReg]) -> usize {
        let mut base = base;
        cpu.write_memory(instr, base);
        base += MemSize::U2.len();
        for &param in params {
            cpu.write_memory(param, base);
            base += param.len();
        }

        return base;
    }

    fn run_and_collect<T: InstrEncode>(mut cpu: &mut Cpu, base: usize, instr: T, size: MemSize, params: &[MemReg]) -> MemReg {
        let result_place = CpuIndex::make_index(3, true, false);
        cpu.regs.cur = base as u64;
        let instr = MemReg::U2(instr.encode(size as u8).0);
        let base = write_instruction(&mut cpu, base, instr, params);
        cpu.write_memory(MemReg::U2(result_place), base);

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
            (UMod, ta % tb),
        ];

        let ta_s: i64 = -8;

        let stests = [
            (IDiv, ta_s /  tb as i64),
            (Sar,  ta_s >> tb),
            (IMod, ta_s % tb as i64)
        ];

        for &size in SIZES.iter() {
            for &(op, expected) in tests.iter() {
                let (indexes, base) = push_args(&mut cpu, &[size.pack(ta), size.pack(tb)]);
                let params  = make_memrefs(&indexes);
                let result  = run_and_collect(&mut cpu, base, op, size, &params);
                assert_eq!(result, size.pack(expected), "instruction: {:?}", op);
            }

            for &(op, expected) in stests.iter() {
                let (indexes, base) = push_args(&mut cpu, &[size.pack(ta_s as u64), size.pack(tb)]);
                let params  = make_memrefs(&indexes);
                let result  = run_and_collect(&mut cpu, base, op, size, &params).unpack_signed();
                assert_eq!(result, expected, "instruction: {:?}", op);
            }
        }
    }

    // #[bench]
    // fn bench_binary_ops(b: &mut Bencher) {
    //     use instruction::Bin::*;

    //     let mut cpu = Cpu::new(100, 10);

    //     b.iter(|| {
    //         let (indexes, base) = push_args(&mut cpu, &[MemReg::U8(1234), MemReg::U8(456)]);
    //         let params  = make_memrefs(&indexes);
    //         let result  = run_and_collect(&mut cpu, base, Add, MemSize::U8, &params);
    //         assert_eq!(result, MemReg::U8(1234 + 456));
    //     })
    // }

    // #[bench]
    // fn bench_10000_loops(b: &mut Bencher) {
    //     use ::cpu::RegBlock;
    //     use ::instruction;

    //     let mut cpu = Cpu::new(100, 10);

    //     let iters = 10000;
    //     // instruction: [size:accumulation]
    //     // 0: [2:0] {counter}
    //     // 1: [8:2] Sub [0] 1 [0]
    //     // 2: [6:10] Test [0] 0
    //     // 3: [6:16] Set 3 %0 ;; set if equal
    //     // 4: [4:22] Jmp %0 2
    //     // 5: [2:26] Halt

    //     let (_indexes, base) = push_args(&mut cpu, &[MemReg::U2(iters)]);
    //     let loop_point = MemReg::U2(CpuIndex::make_index(base as u16, false, false));

    //     let mem_at_0 = MemReg::U2(CpuIndex::make_index(0, false, true));
    //     let reg_at_0 = MemReg::U2(CpuIndex::make_index(RegBlock::index_general(0) as u16, true, false));

    //     let size = MemSize::U2;

    //     let instructions: Vec<(Box<InstrEncode>, Vec<MemReg>)> = vec![
    //         (box instruction::Bin::Sub,
    //             vec![mem_at_0, MemReg::U2(1), mem_at_0]),
    //         (box instruction::CpuManip::Tst,
    //             vec![mem_at_0, MemReg::U2(CpuIndex::make_index(0, false, false))]),
    //         (box instruction::CpuManip::Set,
    //             vec![MemReg::U2(3), reg_at_0]),
    //         (box instruction::CpuManip::Jmp,
    //             vec![reg_at_0, loop_point]),
    //         (box instruction::CpuManip::Halt, vec![])
    //     ];

    //     let mut base = base;

    //     for (instr, args) in instructions.into_iter() {
    //         base = write_instruction(
    //             &mut cpu,
    //             base,
    //             MemReg::U2(instr.encode(size as u8).0),
    //             &args
    //         );
    //     }

    //     println!("Written instructions, base at: {}", base);

    //     b.iter(|| {

    //         cpu.regs.cur = loop_point.unpack();

    //         cpu.running = true;

    //         cpu.exe_loop();

    //     })

    // }

    #[test]
    fn test_unary_ops() {
        use instruction::Un::*;

        let mut cpu = Cpu::new(100, 10);
        let t: i64 = -5;

        let tests = [
            (Binv, !t),
            (Linv, (t == 0) as i64),
            (Neg, -t as i64),
            (Pos, t.abs() as i64)
        ];

        for &size in SIZES.iter() {
            for &(op, expected) in tests.iter() {
                let (indexes, base) = push_args(&mut cpu, &[size.pack(t as u64)]);
                let params  = make_memrefs(&indexes);
                let result  = run_and_collect(&mut cpu, base, op, size, &params).unpack_signed();
                assert_eq!(result, expected, "instruction: {:?}", op);
            }
        }
    }

    #[test]
    fn test_cpu_manip_mov() {
        use instruction::CpuManip::Mov;

        let mut cpu = Cpu::new(100, 10);

        let test_num = 0x5a5a5a5a5a5a5a5a;

        for &size in SIZES.iter() {
            let result_place = CpuIndex::make_index(3, true, false); // ret register

            let (indexes, base) = push_args(&mut cpu, &[size.pack(test_num)]);
            let mut params  = make_memrefs(&indexes);
            params.insert(0, MemReg::U2(result_place));

            cpu.regs.cur = base as u64;

            write_instruction(&mut cpu, base, MemReg::U2(Mov.encode(size as u8).0), &params);

            let instr = cpu.get_instr();
            cpu.run_instr(instr);

            let result = cpu.read(size, result_place);

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
            let (indexes, base) = push_args(&mut cpu, &[size.pack(sign_num as u8 as u64)]);
            let mut params  = make_memrefs(&indexes);
            params.push(MemReg::U2(0));
            let signed_result = run_and_collect(&mut cpu, base, Sxi, size, &params).unpack_signed() as i8;

            let (indexes, base) = push_args(&mut cpu, &[size.pack(usign_num as u64)]);
            let mut params  = make_memrefs(&indexes);
            params.push(MemReg::U2(0));
            let unsign_result = run_and_collect(&mut cpu, base, Sxu, size, &params).unpack() as u8;

            assert_eq!(signed_result,  sign_num);
            assert_eq!(unsign_result, usign_num);
        }
    }

    #[test]
    fn test_cpu_manip_jmp() {
        use instruction::CpuManip::Jmp;
        let jump_location = 10;

        let mut cpu = Cpu::new(100, 10);
        run_and_collect(&mut cpu, 0, Jmp, MemSize::U2, &[MemReg::U2(CpuIndex::make_index(1, false, false)), MemReg::U2(jump_location)]);

        assert_eq!(cpu.regs.cur, jump_location as u64);
    }

    #[test]
    fn test_cpu_manip_set() {
        use instruction::CpuManip::Set;
        use super::CpuFlags;

        let mut cpu = Cpu::new(100, 10);

        cpu.flags = CpuFlags::LE;

        let result = run_and_collect(&mut cpu, 0, Set, MemSize::U1, &[MemReg::U2(1)]).unpack();
        assert_eq!(result, 1);

        let result = run_and_collect(&mut cpu, 0, Set, MemSize::U1, &[MemReg::U2(6)]).unpack();
        assert_eq!(result, 0);
    }

    #[test]
    fn test_cpu_manip_tst() {
        use instruction::CpuManip::Tst;
        use super::CpuFlags;

        let mut cpu = Cpu::new(100, 10);

        cpu.flags = CpuFlags::empty();

        let (indexes, base) = push_args(&mut cpu, &[MemReg::U8(-10 as i64 as u64), MemReg::U8(10)]);
        let params  = make_memrefs(&indexes);
        run_and_collect(&mut cpu, base, Tst, MemSize::U8, &params);

        assert_eq!(cpu.flags, CpuFlags::LS);
    }

    #[test]
    fn test_mem_manip_stks() {
        use instruction::MemManip::Stks;

        let mut cpu = Cpu::new(100, 10);

        let (indexes, base) = push_args(&mut cpu, &[MemReg::U2(100)]);
        let params  = make_memrefs(&indexes);
        run_and_collect(&mut cpu, base, Stks, MemSize::U2, &params);

        assert_eq!(cpu.regs.stk, 100);
    }

    #[test]
    fn test_mem_manip_push_pop() {
        use instruction::MemManip::{Push, Pop};

        let mut cpu = Cpu::new(100, 10);
        let test_num = 0x5a5a5a5a5a5a5a5a;

        cpu.regs.stk = 50;  // dont corrupt memory when writing to the stack

        for &size in SIZES.iter() {
            let param   = size.pack(test_num);
            let (indexes, base) = push_args(&mut cpu, &[param]);
            let params  = make_memrefs(&indexes);

            run_and_collect(&mut cpu, base, Push, size, &params);

            let result = run_and_collect(&mut cpu, 0, Pop, size, &[]);
            assert_eq!(result, param);
        }
    }

    #[test]
    fn test_mem_manip_call_ret() {
        use instruction::MemManip::{Call, Ret};

        let mut cpu = Cpu::new(100, 10);
        let stack_position = 50;
        let base_position  = 20;
        cpu.regs.stk = stack_position;
        cpu.regs.bas = base_position;

        let destination = MemReg::U2(70);
        let (indexes, base) = push_args(&mut cpu, &[destination]);
        let params = make_memrefs(&indexes);

        run_and_collect(&mut cpu, base, Call, MemSize::U2, &params);

        assert_ne!(cpu.regs.stk, stack_position);
        assert_ne!(cpu.regs.bas, base_position);

        run_and_collect(&mut cpu, base, Ret, MemSize::U2, &[]);

        assert_eq!(cpu.regs.stk, stack_position);
        assert_eq!(cpu.regs.bas, base_position);
    }

    // IO not tested because... IO
}

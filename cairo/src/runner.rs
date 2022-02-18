//! This module represents a run of a Cairo program as a series of consecutive
//! execution steps, each of which define the execution logic of Cairo instructions

use crate::flags::*;
use crate::memory::CairoMemory;
use crate::word::{CairoWord, Decomposition};
use ark_ff::Field;

/// A structure to store program counter, allocation pointer and frame pointer
#[derive(Clone, Copy)]
pub struct CairoState<F> {
    /// Program counter: points to address in memory
    pc: F,
    /// Allocation pointer: points to first free space in memory
    ap: F,
    /// Frame pointer: points to the beginning of the stack in memory (for arguments)
    fp: F,
}

impl<F: Field> CairoState<F> {
    /// Creates a new triple of pointers
    pub fn new(pc: F, ap: F, fp: F) -> Self {
        CairoState { pc, ap, fp }
    }
}

/// A data structure to store a current step of Cairo computation
pub struct CairoStep<'a, F> {
    /// current word of the program
    pub mem: &'a mut CairoMemory<F>,
    // comment instr for efficiency
    /// current pointers
    curr: CairoState<F>,
    /// (if any) next pointers
    next: Option<CairoState<F>>,
}

impl<'a, F: Field> CairoStep<'a, F> {
    /// Creates a new Cairo execution step from a step index, a Cairo word, and current pointers
    pub fn new(mem: &mut CairoMemory<F>, ptrs: CairoState<F>) -> CairoStep<F> {
        CairoStep {
            mem,
            curr: ptrs,
            next: None,
        }
    }

    /// This function returns the current word instruction being executed
    fn instr(&mut self) -> CairoWord<F> {
        CairoWord::new(self.mem.read(self.curr.pc).expect("pc points to None cell"))
    }

    /// Executes a Cairo step from the current registers
    pub fn execute(&mut self) {
        // This order is important in order to allocate the memory in time
        let op0 = self.set_op0();
        let (op1_addr, op1, size) = self.set_op1(op0);
        let res = self.set_res(op0, op1);
        let (dst_addr, dst) = self.set_dst();
        // If the Option<> is not a guarantee for continuation of the program, we may be removing this
        let next_pc = self.next_pc(size, res, dst, op1);
        let (next_ap, next_fp) = self.next_apfp(size, res, dst, dst_addr, op1_addr);
        self.next = Some(CairoState::new(
            next_pc.expect("Empty next program counter"),
            next_ap.expect("Empty next allocation pointer"),
            next_fp.expect("Empty next frame pointer"),
        ));
    }

    /// This function computes the first operand address.
    /// Outputs: `op0`
    fn set_op0(&mut self) -> Option<F> {
        let reg = match self.instr().op0_reg() {
            /*0*/ OP0_AP => self.curr.ap, // reads first word from allocated memory
            /*1*/ _ => self.curr.fp, // reads first word from input stack
        }; // no more values than 0 and 1 because op0_reg is one bit
        let op0_addr = reg + self.instr().off_op0();
        let op0 = self.mem.read(op0_addr);
        op0
    }

    /// This function computes the second operand address and content and the instruction size
    /// Panics if the flagset `OP1_SRC` has more than 1 nonzero bit
    /// Inputs: `op0`
    /// Outputs: `(op1_addr, op1, size)`
    fn set_op1(&mut self, op0: Option<F>) -> (F, Option<F>, F) {
        let (reg, size) = match self.instr().op1_src() {
            /*0*/
            OP1_DBL => (op0.expect("None op0 for OP1_DBL"), F::one()), // double indexing, op0 should be positive for address
            /*1*/
            OP1_VAL => (self.curr.pc, F::from(2u32)), // off_op1 will be 1 and then op1 contains an immediate value
            /*2*/ OP1_FP => (self.curr.fp, F::one()),
            /*4*/ OP1_AP => (self.curr.ap, F::one()),
            _ => panic!("Invalid op1_src flagset"),
        };
        let op1_addr = reg + self.instr().off_op1(); // apply second offset to corresponding register
        let op1 = self.mem.read(op1_addr);
        (op1_addr, op1, size)
    }

    /// This function computes the value of the result of the arithmetic operation
    /// Panics if a `jnz` instruction is used with an invalid format
    ///     or if the flagset `RES_LOG` has more than 1 nonzero bit
    /// Inputs: `op0`, `op1`
    /// Outputs: `res`
    fn set_res(&mut self, op0: Option<F>, op1: Option<F>) -> Option<F> {
        let res;
        if self.instr().pc_up() == PC_JNZ {
            /*4*/
            // jnz instruction
            if self.instr().res_log() == RES_ONE /*0*/
                && self.instr().opcode() == OPC_JMP_INC /*0*/
                && self.instr().ap_up() != AP_ADD
            /* not 1*/
            {
                res = Some(F::zero()); // "unused"
            } else {
                panic!("Invalid JNZ instruction");
            }
        } else if self.instr().pc_up() == PC_SIZ /*0*/
            || self.instr().pc_up() == PC_ABS /*1*/
            || self.instr().pc_up() == PC_REL
        /*2*/
        {
            // rest of types of updates
            // common increase || absolute jump || relative jump
            res = {
                match self.instr().res_log() {
                    /*0*/
                    RES_ONE => op1, // right part is single operand
                    /*1*/
                    RES_ADD => Some(
                        op0.expect("None op0 after RES_ADD") + op1.expect("None op1 after RES_ADD"),
                    ), // right part is addition
                    /*2*/
                    RES_MUL => Some(
                        op0.expect("None op0 after RES_MUL") * op1.expect("None op1 after RES_MUL"),
                    ), // right part is multiplication
                    _ => panic!("Invalid res_log flagset"),
                }
            };
        } else {
            // multiple bits take value 1
            panic!("Invalid pc_up flagset");
        }
        res
    }

    /// This function computes the destination address
    /// Outputs: `(dst_addr, dst)`
    fn set_dst(&mut self) -> (F, Option<F>) {
        let reg = match self.instr().dst_reg() {
            /*0*/ DST_AP => self.curr.ap, // read from stack
            /*1*/ _ => self.curr.fp, // read from parameters
        }; // no more values than 0 and 1 because op0_reg is one bit
        let dst_addr = reg + self.instr().off_dst();
        let dst = self.mem.read(dst_addr);
        (dst_addr, dst)
    }

    /// This function computes the next program counter
    /// Panics if the flagset `PC_UP` has more than 1 nonzero bit
    /// Inputs: `size`, `res`, `dst`, `op1`,
    /// Outputs: `next_pc`
    fn next_pc(&mut self, size: F, res: Option<F>, dst: Option<F>, op1: Option<F>) -> Option<F> {
        match self.instr().pc_up() {
            /*0*/
            PC_SIZ => Some(self.curr.pc + size), // common case, next instruction is right after the current one
            /*1*/
            PC_ABS => Some(res.expect("None res after PC_ABS")), // absolute jump, next instruction is in res,
            /*2*/
            PC_REL => Some(self.curr.pc + res.expect("None res after PC_REL")), // relative jump, go to some address relative to pc
            /*4*/
            PC_JNZ => {
                // conditional relative jump (jnz)
                if dst == Some(F::zero()) {
                    Some(self.curr.pc + size) // if condition false, common case
                } else {
                    // if condition true, relative jump with second operand
                    Some(self.curr.pc + op1.expect("None op1 after PC_JNZ"))
                }
            }
            _ => panic!("Invalid pc_up flagset"),
        }
    }

    /// This function computes the next values of the allocation and frame pointers
    /// Panics if in a `call` instruction the flagset [AP_UP] is incorrect
    ///     or if in any other instruction the flagset AP_UP has more than 1 nonzero bit
    ///     or if the flagset `OPCODE` has more than 1 nonzero bit
    /// Inputs: `size`, `res`, `dst`, `dst_addr`, `op1_addr`
    /// Outputs: `(next_ap, next_fp)`
    fn next_apfp(
        &mut self,
        size: F,
        res: Option<F>,
        dst: Option<F>,
        dst_addr: F,
        op1_addr: F,
    ) -> (Option<F>, Option<F>) {
        let (next_ap, next_fp);
        // The following branches don't include the assertions. That is done in the verification.
        if self.instr().opcode() == OPC_CALL {
            /*1*/
            // "call" instruction
            self.mem.write(self.curr.ap, self.curr.fp); // Save current fp
            self.mem.write(self.curr.ap + F::one(), self.curr.pc + size); // Save next instruction
                                                                          // Update fp
            next_fp = Some(self.curr.ap + F::from(2u32)); // pointer for next frame is after current fp and instruction after call
                                                          // Update ap
            match self.instr().ap_up() {
                /*0*/
                AP_Z2 => next_ap = Some(self.curr.ap + F::from(2u32)), // two words were written so advance 2 positions
                _ => panic!("ap increment in call instruction"), // ap increments not allowed in call instructions
            };
        } else if self.instr().opcode() == OPC_JMP_INC /*0*/
            || self.instr().opcode() == OPC_RET /*2*/
            || self.instr().opcode() == OPC_AEQ
        /*4*/
        {
            // rest of types of instruction
            // jumps and increments || return || assert equal
            match self.instr().ap_up() {
                /*0*/ AP_Z2 => next_ap = Some(self.curr.ap), // no modification on ap
                /*1*/
                AP_ADD => {
                    // ap += <op> should be larger than current ap
                    next_ap = Some(self.curr.ap + res.expect("None res after AP_ADD"))
                }
                /*2*/ AP_ONE => next_ap = Some(self.curr.ap + F::one()), // ap++
                _ => panic!("Invalid ap_up flagset"),
            }

            match self.instr().opcode() {
                /*0*/
                OPC_JMP_INC => next_fp = Some(self.curr.fp), // no modification on fp
                /*2*/
                OPC_RET => next_fp = Some(dst.expect("None dst after OPC_RET")), // ret sets fp to previous fp that was in [ap-2]
                /*4*/
                OPC_AEQ => {
                    // The following conditional is a fix that is not explained in the whitepaper
                    // The goal is to distinguish two types of ASSERT_EQUAL where one checks that
                    // dst = res , but in order for this to be true, one sometimes needs to write
                    // the res in mem(dst_addr) and sometimes write dst in mem(res_dir). The only
                    // case where res can be None is when res = op1 and thus res_dir = op1_addr
                    if res.is_none() {
                        self.mem
                            .write(op1_addr, dst.expect("None dst after OPC_AEQ"));
                    // res = dst
                    } else {
                        self.mem
                            .write(dst_addr, res.expect("None res after OPC_AEQ"));
                        // dst = res
                    }
                    next_fp = Some(self.curr.fp); // no modification on fp
                }
                _ => {
                    panic!("This case must never happen")
                }
            }
        } else {
            panic!("Invalid opcode flagset");
        }
        (next_ap, next_fp)
    }
}

/// This struct stores the needed information to run a program
pub struct CairoProgram<'a, F> {
    /// total number of steps
    steps: F,
    /// full execution memory
    mem: &'a mut CairoMemory<F>,
    /// initial computation registers
    ini: CairoState<F>,
    /// final computation pointers
    fin: CairoState<F>,
}

impl<'a, F: Field> CairoProgram<'a, F> {
    /// Creates a Cairo execution from the public information (memory and initial pointers)
    pub fn new(mem: &mut CairoMemory<F>, pc: u64, ap: u64) -> CairoProgram<F> {
        let mut prog = CairoProgram {
            steps: F::zero(),
            mem,
            ini: CairoState::new(F::from(pc), F::from(ap), F::from(ap)),
            fin: CairoState::new(F::zero(), F::zero(), F::zero()),
        };
        prog.execute();
        prog
    }

    /// Outputs the total number of steps of the execution carried out by the runner
    pub fn get_steps(&self) -> F {
        self.steps
    }

    /// Outputs the final value of the pointers after the execution carried out by the runner
    pub fn get_final(&self) -> CairoState<F> {
        self.fin
    }

    /// This function simulates an execution of the Cairo program received as input.
    /// It generates the full memory stack and the execution trace
    fn execute(&mut self) {
        // set finishing flag to false, as it just started
        let mut end = false;
        // saves local copy of the initial (claimed) pointers of the program
        let mut curr = self.ini;
        let mut next = self.ini;
        // first timestamp
        let mut n: u64 = 0;
        // keep executing steps until the end is reached
        while !end {
            // create current step of computation
            let mut step = CairoStep::new(self.mem, next);
            // save current value of the pointers
            curr = step.curr;
            // execute current step and increase time counter
            step.execute();
            n += 1;
            match step.next {
                None => end = true, // if find no next pointers, end
                _ => {
                    // if there are next pointers
                    end = false;
                    // update next value of pointers
                    next = step.next.expect("Empty next pointers");
                    if curr.ap <= next.pc {
                        // if reading from unallocated memory, end
                        end = true;
                    }
                }
            }
        }
        self.steps = F::from(n);
        self.fin = CairoState::new(curr.pc, curr.ap, curr.fp);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helper::CairoFieldHelpers;
    use mina_curves::pasta::fp::Fp as F;

    #[test]
    fn test_cairo_step() {
        // This tests that CairoStep works for a 2 word instruction
        //    tempvar x = 10;
        let instrs = vec![
            F::from(0x480680017fff8000u64),
            F::from(10u64),
            F::from(0x208b7fff7fff7ffeu64),
        ];
        let mut mem = CairoMemory::new(instrs);
        // Need to know how to find out
        // Is it final ap and/or final fp? Will write to starkware guys to learn about this
        mem.write(F::from(4u32), F::from(7u32));
        mem.write(F::from(5u32), F::from(7u32));
        let ptrs = CairoState::new(F::from(1u32), F::from(6u32), F::from(6u32));
        let mut step = CairoStep::new(&mut mem, ptrs);

        step.execute();
        assert_eq!(step.next.unwrap().pc, F::from(3u32));
        assert_eq!(step.next.unwrap().ap, F::from(7u32));
        assert_eq!(step.next.unwrap().fp, F::from(6u32));

        println!("{}", step.mem);
    }

    #[test]
    fn test_cairo_program() {
        let instrs = vec![
            F::from(0x480680017fff8000u64),
            F::from(10u64),
            F::from(0x208b7fff7fff7ffeu64),
        ];
        let mut mem = CairoMemory::<F>::new(instrs);
        // Need to know how to find out
        // Is it final ap and/or final fp? Will write to starkware guys to learn about this
        mem.write(F::from(4u32), F::from(7u32)); //beginning of output
        mem.write(F::from(5u32), F::from(7u32)); //end of output
        let prog = CairoProgram::new(&mut mem, 1, 6);
        println!("{}", prog.mem);
    }

    #[test]
    fn test_cairo_output() {
        // This is a test for a longer program, involving builtins, imports and outputs
        // One can generate more tests here: https://www.cairo-lang.org/playground/
        /*
        %builtins output
        from starkware.cairo.common.serialize import serialize_word
        func main{output_ptr : felt*}():
            tempvar x = 10
            tempvar y = x + x
            tempvar z = y * y + x
            serialize_word(x)
            serialize_word(y)
            serialize_word(z)
            return ()
        end
        */
        let instrs: Vec<i128> = vec![
            0x400380007ffc7ffd,
            0x482680017ffc8000,
            1,
            0x208b7fff7fff7ffe,
            0x480680017fff8000,
            10,
            0x48307fff7fff8000,
            0x48507fff7fff8000,
            0x48307ffd7fff8000,
            0x480a7ffd7fff8000,
            0x48127ffb7fff8000,
            0x1104800180018000,
            -11,
            0x48127ff87fff8000,
            0x1104800180018000,
            -14,
            0x48127ff67fff8000,
            0x1104800180018000,
            -17,
            0x208b7fff7fff7ffe,
            /*41, // beginning of outputs
            44,   // end of outputs
            44,   // input
            */
        ];

        let mut mem = CairoMemory::<F>::new(F::vec_to_field(&instrs));
        // Need to know how to find out
        mem.write(F::from(21u32), F::from(41u32)); // beginning of outputs
        mem.write(F::from(22u32), F::from(44u32)); // end of outputs
        mem.write(F::from(23u32), F::from(44u32)); //end of program
        let prog = CairoProgram::new(&mut mem, 5, 24);
        assert_eq!(prog.get_final().pc, F::from(20u32));
        assert_eq!(prog.get_final().ap, F::from(41u32));
        assert_eq!(prog.get_final().fp, F::from(24u32));
        println!("{}", prog.mem);
        assert_eq!(prog.mem.read(F::from(24u32)).unwrap(), F::from(10u32));
        assert_eq!(prog.mem.read(F::from(25u32)).unwrap(), F::from(20u32));
        assert_eq!(prog.mem.read(F::from(26u32)).unwrap(), F::from(400u32));
        assert_eq!(prog.mem.read(F::from(27u32)).unwrap(), F::from(410u32));
        assert_eq!(prog.mem.read(F::from(28u32)).unwrap(), F::from(41u32));
        assert_eq!(prog.mem.read(F::from(29u32)).unwrap(), F::from(10u32));
        assert_eq!(prog.mem.read(F::from(30u32)).unwrap(), F::from(24u32));
        assert_eq!(prog.mem.read(F::from(31u32)).unwrap(), F::from(14u32));
        assert_eq!(prog.mem.read(F::from(32u32)).unwrap(), F::from(42u32));
        assert_eq!(prog.mem.read(F::from(33u32)).unwrap(), F::from(20u32));
        assert_eq!(prog.mem.read(F::from(34u32)).unwrap(), F::from(24u32));
        assert_eq!(prog.mem.read(F::from(35u32)).unwrap(), F::from(17u32));
        assert_eq!(prog.mem.read(F::from(36u32)).unwrap(), F::from(43u32));
        assert_eq!(prog.mem.read(F::from(37u32)).unwrap(), F::from(410u32));
        assert_eq!(prog.mem.read(F::from(38u32)).unwrap(), F::from(24u32));
        assert_eq!(prog.mem.read(F::from(39u32)).unwrap(), F::from(20u32));
        assert_eq!(prog.mem.read(F::from(40u32)).unwrap(), F::from(44u32));
        assert_eq!(prog.mem.read(F::from(41u32)).unwrap(), F::from(10u32));
        assert_eq!(prog.mem.read(F::from(42u32)).unwrap(), F::from(20u32));
        assert_eq!(prog.mem.read(F::from(43u32)).unwrap(), F::from(410u32));
    }
}

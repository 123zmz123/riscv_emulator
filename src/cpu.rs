#![allow(dead_code)]

use crate::bus::*;
use crate::exception::*;
use crate::param::*;
use crate::csr::*;

type Mode = u64;
const User: Mode = 0b00;
const Supervisor: Mode = 0b01;
const Machine: Mode = 0b11;

pub struct Cpu{
    pub regs: [u64; 32],
    pub pc: u64,
    pub mode: Mode,
    pub bus: Bus,
    pub csr: Csr,
}

const RVABI: [&str; 32] = [
     "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", 
    "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5", 
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", 
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6",
];

impl Cpu {
    pub fn new(code: Vec<u8>) -> Self {
        let mut regs = [0; 32];
        regs[2] = DRAM_END;
        let pc = DRAM_BASE;
        let bus = Bus::new(code);
        let csr = Csr::new();
        let mode = Machine;
        Self {regs, pc, bus,csr,mode}
    }

    pub fn reg(&self, r: &str) -> u64 {
        match RVABI.iter().position(|&x| x == r) {
            Some(i) => self.regs[i],
            None => match r {
                "pc" => self.pc,
                "fp" => self.reg("s0"),
                r if r.starts_with("x") => {
                    if let Ok(i) = r[1..].parse::<usize>() {
                        if i <= 31 { return self.regs[i]; } 
                        panic!("Invalid register {}", r);
                    }
                    panic!("Invalid register {}", r);
                }
                "mhartid"=>self.csr.load(MHARTID),
                "mstatus"=>self.csr.load(MSTATUS),
                "mtvec"=>self.csr.load(MTVEC), // trap vec array address
                "mepc"=>self.csr.load(MEPC), // machine exception pc
                "mcause"=>self.csr.load(MCAUSE),// indicate which event cause the trap?
                "mtval"=>self.csr.load(MTVAL),// faulting information in different mode
                "medeleg"=>self.csr.load(MEDELEG),// the recorded trap can handle by lower privilege level.
                "mscratch"=>self.csr.load(MSCRATCH),// pointer to a context switch
                "MIP"=>self.csr.load(MIP), // M-Mode what intterrupt are pending?
                "mcounteren"=>self.csr.load(MCOUNTEREN),
                "sstatus"=>self.csr.load(SSTATUS), // S-mode current processor state.
                "stvec"=>self.csr.load(STVEC), //S-mode trap vec array address
                "sepc"=>self.csr.load(SEPC),// S-Mode exception PC
                "scause"=>self.csr.load(SCAUSE),// S-Mode indicate which event cause the trap
                "stval"=>self.csr.load(STVAL),// additional fault information when trap occured
                "sscratch"=>self.csr.load(SSCRATCH),// S-Mode pointer to context switch
                "SIP"=>self.csr.load(SIP),// S-mode what interrupt are pending
                "SATP"=>self.csr.load(SATP),//S-mode page table related regs
                _ => panic!("Invalid register {}", r),
            }
        }
    }

    pub fn dump_pc(&self) {
        println!("{:-^80}","PC register");
        println!("PC={:#x}\n",self.pc);
    }

    pub fn dump_registers(&mut self) {
        println!("{:-^80}", "registers");
        let mut output = String::new();
        self.regs[0] = 0;

        for i in (0..32).step_by(4) {
            let i0 = format!("x{}", i);
            let i1 = format!("x{}", i + 1); 
            let i2 = format!("x{}", i + 2);
            let i3 = format!("x{}", i + 3); 
            let line = format!(
                "{:3}({:^4}) = {:<#18x} {:3}({:^4}) = {:<#18x} {:3}({:^4}) = {:<#18x} {:3}({:^4}) = {:<#18x}\n",
                i0, RVABI[i], self.regs[i], 
                i1, RVABI[i + 1], self.regs[i + 1], 
                i2, RVABI[i + 2], self.regs[i + 2], 
                i3, RVABI[i + 3], self.regs[i + 3],
            );
            output = output + &line;
        }

        println!("{}", output);
    }
    pub fn dump_csrs(&self) {
        self.csr.dump_csrs();
    }
    pub fn handle_exception(&mut self, e:Exception){
        let pc = self.pc;
        let mode = self.mode;
        let cause = e.code();
        // by default all exception were handled in M mode, but by mdelegate reg some can hanle in lower privelege
        // mode
        let trap_in_s_mode = mode <= Supervisor && self.csr.is_medelegated(cause);
        let (STATUS, TVEC, CAUSE, TVAL,EPC,MASK_PIE,pie_i,MASK_IE,ie_i,MASK_PP,pp_i) 
            = if trap_in_s_mode{
                self.mode = Supervisor;
                (SSTATUS,STVEC,SCAUSE,STVAL,SEPC,MASK_SPIE,5,MASK_SIE,1,MASK_SPP,8) // ref rv64 sstatus define

            }else{
                self.mode = Machine;
                 (MSTATUS, MTVEC, MCAUSE, MTVAL, MEPC, MASK_MPIE, 7, MASK_MIE, 3, MASK_MPP, 11)
            };
        // pc = vector table address
        self.pc = self.csr.load(TVEC) & !0b11;
        // record the pc number that encounter the exception
        self.csr.store(EPC, pc);
        self.csr.store(CAUSE, cause);
        self.csr.store(TVAL, e.value());
        let mut status = self.csr.load(STATUS);
        let ie = (status & MASK_IE) >> ie_i;
        status = (status & !MASK_PIE) | (ie << pie_i);
        status &= !MASK_IE;
        status = (status & !MASK_PP) | (mode << pp_i);
        self.csr.store(STATUS, status);
    }
    pub fn load(&mut self, addr: u64, size: u64)->Result<u64, Exception>{
        self.bus.load(addr, size)
    }

    pub fn store(&mut self, addr:u64, size: u64, value: u64)->Result<(), Exception>{
        self.bus.store(addr, size, value)
    }

    pub fn fetch(&mut self)->Result<u64,Exception>{
        match self.bus.load(self.pc, 32) {
            Ok(instr) => Ok(instr),
            Err(_e) => Err(Exception::InstructionAccessFault(self.pc)),
        }
    }

    pub fn update_pc(&mut self)->Result<u64, Exception>{
        return Ok(self.pc + 4);
    }

    pub fn execute(&mut self, instr:u64)->Result<u64,Exception>{
        let opcode = instr & 0x0000007f;
        let rd = ((instr & 0x00000f80) >> 7) as usize;
        let rs1 = ((instr & 0x000f8000) >> 15) as usize;
        let rs2 = ((instr & 0x01f00000) >> 20) as usize;
        let funct3 = (instr & 0x00007000) >> 12;
        let funct7 = (instr & 0xfe000000) >> 25;
        // x0 always be zero;
        self.regs[0] = 0; 

        match opcode {
            0x03 => { // lb,lh,lw,lbu,lhu
                let imm = ((instr as i32 as i64) >> 20) as u64;
                let addr = self.regs[rs1].wrapping_add(imm);
                match funct3 {
                    0x0 => {
                        // lb
                        let val = self.load(addr, 8)?;
                        self.regs[rd] = val as i8 as i64 as u64;
                        return self.update_pc();
                    }

                    0x1 => {
                        // lh
                        let val = self.load(addr, 16)?;
                        self.regs[rd] = val as i16 as i64 as u64;
                        return self.update_pc();
                    }

                    0x2 => {
                        // lw
                        let val = self.load(addr, 32)?;
                        self.regs[rd] = val as i32 as i64 as u64;
                        return self.update_pc();
                    }

                    0x3 => {
                        // ld
                        let val = self.load(addr, 64)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x4 => {
                        // lbu
                        let val = self.load(addr, 8)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x5 => {
                        // lhu
                        let val = self.load(addr, 16)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x6 => {
                        // lwu
                        let val = self.load(addr, 32)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }

            0x0f => {
                match funct3 {
                    // we do not implement fence at here
                    0x0 => {
                        return self.update_pc();
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }

            0x13 => { // addi,slti,sltiu,xori,ori,andi
                let imm = ((instr & 0xfff00000) as i32 as i64 >> 20) as u64;
                let shamt = (imm & 0x3f) as u32;
                match funct3 {
                    0x0 => {
                        // addi
                        self.regs[rd] = self.regs[rs1].wrapping_add(imm);
                        return self.update_pc();
                    }

                    0x1 => {
                        // slli
                        self.regs[rd] = self.regs[rs1] << shamt;
                        return self.update_pc();
                    }

                    0x2 => {
                        // slti
                        self.regs[rd] = if (self.regs[rs1] as i64) < (imm as i64) { 1 } else { 0 };
                        return self.update_pc();
                    }

                    0x3 => {
                        // sltiu
                        self.regs[rd] = if self.regs[rs1] < imm { 1 } else { 0 };
                        return self.update_pc();
                    }

                    0x4 => {
                        //xori
                        self.regs[rd] = self.regs[rs1]^imm;
                        return self.update_pc();
                    }
                    0x5 => {
                        match funct7 >> 1 {
                            //srli
                            0x00 => {
                                self.regs[rd] = self.regs[rs1].wrapping_shr(shamt);
                                return self.update_pc();
                            }

                            //srai
                            0x10 => {
                                self.regs[rd]=(self.regs[rs1] as i64).wrapping_shr(shamt) as u64;
                                return self.update_pc();
                            }
                            _ => Err(Exception::IllegalInstruction(instr)),
                            
                        }
                    }

                    0x6 => { //ori
                        self.regs[rd] = self.regs[rs1] | imm;
                        return self.update_pc();
                    }
                    0x7 => { 
                        self.regs[rd]=self.regs[rs1]&imm; // andi
                        return self.update_pc();
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            
            0x17 => {
                // auipc
                let imm = (instr & 0xfffff000) as i32 as i64 as u64;
                self.regs[rd] = self.pc.wrapping_add(imm);
                return self.update_pc();
            }

            0x1b => { //
                let imm = ((instr as i32 as i64)>>20) as u64;
                let shamt = (imm & 0x1f) as u32;
                match funct3 {
                    0x0 => {
                        //addiw
                        self.regs[rd]=self.regs[rs1].wrapping_add(imm) as i32 as i64 as u64;
                        return self.update_pc();
                    }
                    0x1 => {
                        //slliw
                        self.regs[rd] = self.regs[rs1].wrapping_shl(shamt) as i32 as i64 as u64;
                        return self.update_pc();
                    }
                    0x5 => {
                        match funct7 {
                            0x00 => {
                                //srliw
                                self.regs[rd] = (self.regs[rs1] as u32).wrapping_shr(shamt) as i32
                                    as i64 as u64;
                                return self.update_pc();
                            }
                            0x20 => {
                                // sraiw
                                self.regs[rd] = 
                                    (self.regs[rs1] as i32).wrapping_shr(shamt) as i64 as u64;
                                return self.update_pc();
                            }

                            _ => Err(Exception::IllegalInstruction(instr)),
                        }
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            
            0x23 => {

                let imm = (((instr & 0xfe000000) as i32 as i64 >> 20) as u64) | ((instr >> 7) & 0x1f);
                let addr = self.regs[rs1].wrapping_add(imm);
                match funct3 {
                    0x0 => {self.store(addr,8,self.regs[rs2])?;self.update_pc()},//sb
                    0x1 => {self.store(addr,16,self.regs[rs2])?;self.update_pc()},//sh
                    0x2 => {self.store(addr,32,self.regs[rs2])?;self.update_pc()},//sw
                    0x3 => {self.store(addr,64,self.regs[rs2])?;self.update_pc()},//sd
                    _ => unreachable!(),
                }
            }

            0x2f => { // atomic function which means all the operation happen at a single time unit
                let funct5 = (funct7 & 0b1111100) >> 2;
                let _aq = (funct7 & 0b0000010) >> 1;
                let _rl = funct7 & 0b0000001;
                match (funct3,funct5) {
                    (0x2,0x00)=>{
                        // amoadd.w
                        let t = self.load(self.regs[rs1],32)?;
                        self.store(self.regs[rs1],32,t.wrapping_add(self.regs[rs2]))?;
                        self.regs[rd]=t;
                        return self.update_pc();
                    }
                    (0x3,0x00)=>{
                        //amoadd.d
                        let t = self.load(self.regs[rs1],64)?;
                        self.store(self.regs[rs1],64,t.wrapping_add(self.regs[rs2]))?;
                        self.regs[rd]=t;
                        return self.update_pc();
                    }
                    (0x2,0x01)=>{
                        //amoswap.w
                        let t = self.load(self.regs[rs1],32)?;
                        self.store(self.regs[rs1],32,self.regs[rs2])?;
                        self.regs[rd]=t;
                        return self.update_pc();
                    }
                    (0x3,0x01)=>{
                        //amoswap.d
                        let t = self.load(self.regs[rs1],64)?;
                        self.store(self.regs[rs1],64,self.regs[rs2])?;
                        self.regs[rd]=t;
                        return self.update_pc();
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            0x33 => {
                let shamt = ((self.regs[rs2] & 0x3f) as u64) as u32;
                match (funct3, funct7) {
                    (0x0, 0x00) => { 
                        // add
                        self.regs[rd] = self.regs[rs1].wrapping_add(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x0, 0x01) => {
                        // mul
                        self.regs[rd] = self.regs[rs1].wrapping_mul(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x0, 0x20) => {
                        // sub
                        self.regs[rd]=self.regs[rs1].wrapping_sub(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x1, 0x00) => {
                        // sll 
                        self.regs[rd]=self.regs[rs1].wrapping_shl(shamt);
                        return self.update_pc();
                    }

                    (0x2, 0x00) => {
                        // slt
                        self.regs[rd] = if (self.regs[rs1] as i64) < (self.regs[rs2] as i64) { 1 } else { 0 };
                        return self.update_pc();
                    }

                    (0x3, 0x00) => {
                        // sltu
                        self.regs[rd] = if self.regs[rs1] < self.regs[rs2] { 1 } else { 0 };
                        return self.update_pc();
                    }

                    (0x4, 0x00) => {
                        // xor
                        self.regs[rd] = self.regs[rs1]^self.regs[rs2];
                        return self.update_pc();
                    }

                    (0x5, 0x00) => {
                        // srl
                        self.regs[rd] = self.regs[rs1].wrapping_shr(shamt);
                        return self.update_pc();
                    }

                    (0x5, 0x20) => {
                        // sra
                        self.regs[rd] = (self.regs[rs1] as i64).wrapping_shr(shamt) as u64;
                        return self.update_pc();
                    }

                    (0x6, 0x00) => {
                        // or
                        self.regs[rd] = self.regs[rs1] | self.regs[rs2];
                        return self.update_pc();
                    }

                    (0x7, 0x00) => {
                        // and
                        self.regs[rd] = self.regs[rs1] & self.regs[rs2];
                        return self.update_pc();
                    }

                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }   
            
            0x37 => {
                // lui load imm upper bound to rd
                self.regs[rd] = (instr & 0xfffff000) as i32 as i64 as u64;
                return self.update_pc();
            }

            0x3b => {
                let shamt = (self.regs[rs2] & 0x1f) as u32;
                match (funct3, funct7) {
                    (0x0, 0x00) => {
                        // addw
                        self.regs[rd] =
                            self.regs[rs1].wrapping_add(self.regs[rs2]) as i32 as i64 as u64;
                        return self.update_pc();
                        
                    }

                    (0x0, 0x20) => {
                        // subw
                        self.regs[rd] = 
                            ((self.regs[rs1].wrapping_sub(self.regs[rs2])) as i32) as u64;
                        return self.update_pc();
                    }

                    (0x1, 0x00) => {
                        // sllw
                        self.regs[rd] = (self.regs[rs1] as u32).wrapping_shl(shamt) as i32 as u64;
                        return self.update_pc();
                    }

                    (0x5, 0x00) => {
                        // srlw
                        self.regs[rd] = (self.regs[rs1] as u32).wrapping_shr(shamt) as i32 as u64;
                        return self.update_pc();
                    }
                    (0x5,0x01) => {
                        // divu
                        self.regs[rd] = match self.regs[rs2] {
                            0 => 0xffffffff_ffffffff,
                            _ => {
                                let dividend = self.regs[rs1];
                                let divisor = self.regs[rs2];
                                dividend.wrapping_div(divisor)
                            }
                        };
                        return self.update_pc();
                    }
                    (0x5, 0x20) => {
                        // sraw
                        self.regs[rd] = ((self.regs[rs1] as i32) >> (shamt as i32)) as u64;
                        return self.update_pc();
                    }
                    (0x7,0x01) => {
                        // remuw
                        self.regs[rd] = match self.regs[rs2] {
                            0 => self.regs[rs1],
                            _ => {
                                let dividend = self.regs[rs1] as u32;
                                let divisor = self.regs[rs2] as u32;
                                dividend.wrapping_rem(divisor) as i32 as u64
                            }
                        };
                        return self.update_pc();
                    }

                    _ => Err(Exception::IllegalInstruction(instr)),

                }
            }
            0x63 => {
                let imm = (((instr & 0x80000000) as i32 as i64 >> 19) as u64)
                    | ((instr & 0x80) << 4) // imm[11]
                    | ((instr >> 20) & 0x7e0) // imm[10:5]
                    | ((instr >> 7) & 0x1e); // imm[4:1]
                match funct3 {
                    0x0 => {
                        // beq
                        if self.regs[rs1] == self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x1 => {
                        // bne
                        if self.regs[rs1] != self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x4 => {
                        // blt
                        if (self.regs[rs1] as i64) < (self.regs[rs2] as i64) {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x5 => {
                        // bge
                        if (self.regs[rs1] as i64) >= (self.regs[rs2] as i64) {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x6 => {
                        // bltu
                        if self.regs[rs1] < self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x7 => {
                        // bgeu
                        if self.regs[rs1] >= self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            0x67 => {
                // jalr
                let t = self.pc + 4;
                let imm = ((((instr & 0xfff00000) as i32) as i64) >> 20) as u64;
                let new_pc = (self.regs[rs1].wrapping_add(imm)) & !1;

                self.regs[rd] = t;
                return Ok(new_pc);
            }

            0x6f => {
                // jal
                self.regs[rd] = self.pc + 4;
                let imm = (((instr & 0x80000000) as i32 as i64 >> 11) as u64) // imm[20]
                    | (instr & 0xff000) // imm[19:12]
                    | ((instr >> 9) & 0x800) // imm[11]
                    | ((instr >> 20) & 0x7fe); // imm[10:1]
                return Ok(self.pc.wrapping_add(imm));
            }

            0x73 => {
                let csr_addr = ((instr&0xfff00000)>>20) as usize;
                match funct3 {
                    0x0 => {
                        match(rs2,funct7){
                            (0x0,0x0) => {
                                match self.mode {
                                    User => Err(Exception::EnvironmentCallFromUMode(self.pc)),
                                    Supervisor => Err(Exception::EnvironmentCallFromSMode(self.pc)),
                                    Machine => Err(Exception::EnvironmentCallFromMMode(self.pc)),
                                    _ => unreachable!(),
                                }
                            }
                            (0x1,0x0)=>{
                                // ebreak
                                // debugger raise a request breakpoint
                                return Err(Exception::Breakpoint(self.pc));
                            }
                            (0x2,0x8)=>{
                                   // sret
                                // When the SRET instruction is executed to return from the trap
                                // handler, the privilege level is set to user mode if the SPP
                                // bit is 0, or supervisor mode if the SPP bit is 1. The SPP bit
                                // is SSTATUS[8].
                                let mut sstatus = self.csr.load(SSTATUS);
                                self.mode = (sstatus & MASK_SPP) >> 8;
                                // The SPIE bit is SSTATUS[5] and the SIE bit is the SSTATUS[1]
                                let spie = (sstatus & MASK_SPIE) >> 5;
                                // set SIE = SPIE
                                sstatus = (sstatus & !MASK_SIE) | (spie << 1);
                                // set SPIE = 1
                                sstatus |= MASK_SPIE;
                                // set SPP the least privilege mode (u-mode)
                                sstatus &= !MASK_SPP;
                                self.csr.store(SSTATUS, sstatus);
                                // set the pc to CSRs[sepc].
                                // whenever IALIGN=32, bit sepc[1] is masked on reads so that it appears to be 0. This
                                // masking occurs also for the implicit read by the SRET instruction. 
                                let new_pc = self.csr.load(SEPC) & !0b11;
                                return Ok(new_pc);
                            }
                            (0x2,0x18) => {
                                 // mret
                                 let mut mstatus = self.csr.load(MSTATUS);
                                 // MPP is two bits wide at MSTATUS[12:11]
                                 self.mode = (mstatus & MASK_MPP) >> 11;
                                 // The MPIE bit is MSTATUS[7] and the MIE bit is the MSTATUS[3].
                                 let mpie = (mstatus & MASK_MPIE) >> 7;
                                 // set MIE = MPIE
                                 mstatus = (mstatus & !MASK_MIE) | (mpie << 3);
                                 // set MPIE = 1
                                 mstatus |= MASK_MPIE;
                                 // set MPP the least privilege mode (u-mode)
                                 mstatus &= !MASK_MPP;
                                 // If MPP != M, sets MPRV=0
                                 mstatus &= !MASK_MPRV;
                                 self.csr.store(MSTATUS, mstatus);
                                 // set the pc to CSRs[mepc].
                                 let new_pc = self.csr.load(MEPC) & !0b11;
                                 return Ok(new_pc);
                            }
                            (_,0x9)=>{
                                // sfence.vma
                                // Do nothing.
                                return self.update_pc();
                            }
                            _ => Err(Exception::IllegalInstruction(instr)),
                        }
                    }
                    0x1 => {
                        // csrrw
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,self.regs[rs1]);
                        self.regs[rd] = t;
                        return self.update_pc();
                    }

                    0x2 => {
                        // csrrs
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr, t | self.regs[rs1]);
                        self.regs[rd]=t;
                        return self.update_pc();
                    }

                    0x3 => {
                        // csrrc
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,t&(!self.regs[rs1]));
                        self.regs[rd]=t;
                        return self.update_pc();
                    }

                    0x5 => {
                        // csrrwi
                        let zimm = rs1 as u64;
                        self.regs[rd]=self.csr.load(csr_addr);
                        self.csr.store(csr_addr,zimm);
                        return self.update_pc();
                    }

                    0x6 => {
                        //csrrsi
                        let zimm = rs1 as u64;
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr, t|zimm);
                        self.regs[rd]=t;
                        return self.update_pc();
                    }

                    0x7 => {
                        //csrrci
                        let zimm = rs1 as u64;
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,t & (!zimm));
                        self.regs[rd]=t;
                        return self.update_pc();
                    }
                    
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            _ => Err(Exception::IllegalInstruction(instr)),
        }
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;
    use std::io::{Write,Read};
    use std::process::Command;
    use super::*;

    fn generate_rv_assembly(c_src: &str) { // .c -> .s
        let cc = "clang";
        let ouptput = Command::new(cc).arg("-S")
                                            .arg(c_src)
                                            .arg("-nostdlib")
                                            .arg("-march=rv64g")
                                            .arg("-mabi=lp64")
                                            .arg("--target=riscv64")
                                            .arg("-mno-relax")
                                            .output()
                                            .expect("Failed to generate riscv assembly");
        println!("{}",String::from_utf8_lossy(&ouptput.stderr));
    }

    fn generate_rv_obj(assemly:&str){
        let cc = "clang";
        let pieces: Vec<&str> = assemly.split(".").collect();
        let output = Command::new(cc).arg("-Wl,-Ttext=0x0")
                                            .arg("-nostdlib")
                                            .arg("-march=rv64g")
                                            .arg("-mabi=lp64")
                                            .arg("--target=riscv64")
                                            .arg("-mno-relax")
                                            .arg("-o")
                                            .arg(&pieces[0]) //obj file name
                                            .arg(assemly)
                                            .output()
                                            .expect("Failed to generate rv object");
        println!("{}", String::from_utf8_lossy(&output.stderr));
    }

    fn generate_rv_binary(obj:&str){
        let objcopy = "llvm-objcopy";
        let output = Command::new(objcopy).arg("-O")
                                              .arg("binary")
                                              .arg(obj)
                                              .arg(obj.to_owned()+".bin")
                                              .output()
                                              .expect("Failed to generate rv binary");

        println!("{}",String::from_utf8_lossy(&output.stderr));
    }

    fn rv_helper(code:&str,testname:&str,n_clock:usize)->Result<Cpu,std::io::Error>{
        let filename = testname.to_owned() + ".s";
        let mut file = File::create(&filename)?;
        file.write(&code.as_bytes())?;
        generate_rv_obj(&filename);
        generate_rv_binary(testname);
        let mut file_bin = File::open(testname.to_owned() + ".bin")?;
        let mut code = Vec::new();
        file_bin.read_to_end(&mut code)?;
        let mut cpu = Cpu::new(code);

        for _i in 0..n_clock {
            let instr = match cpu.fetch() {
                Ok(instr)=>instr,
                Err(_err)=>break,
            };
            match cpu.execute(instr){
                Ok(new_pc) => cpu.pc=new_pc,
                Err(err) => println!("{}",err),
            };

        }
        return Ok(cpu);
    }

    macro_rules! riscv_test {
        ($code:expr, $name:expr, $clock:expr, $($check:expr => $expect:expr),*) => {
           match rv_helper($code,$name,$clock) {
            Ok(cpu)=>{
                $(assert_eq!(cpu.reg($check),$expect);)*
            }
            Err(e)=>{println!("error:{}",e);assert!(false);}
           }
        };
    }

    #[test]
    fn test_add(){
        let code = "addi x31, x0, 42";
        riscv_test!(code,"test_addi",1,"x31" => 42);
        // match rv_helper(code,"test_addi",1) {
        //     Ok(cpu) => assert_eq!(cpu.regs[31],42),
        //     Err(e) => {println!("error:{}",e); assert!(false);}
        // }
    }
    #[test]
    fn test_simple() {
        let code = "
        addi	sp,sp,-16
        sd	s0,8(sp)
        addi	s0,sp,16
        li	a5,42
        mv	a0,a5
        ld	s0,8(sp)
        addi	sp,sp,16
        jr	ra
        ";
        riscv_test!(code,"test_simple",20,"a0"=>42);
    }

    #[test]
    fn test_auipc(){
        let code ="auipc a0,42";
        riscv_test!(code,"test_auipc",1,"a0"=>DRAM_BASE+(42<<12));
    }

    #[test]
    fn test_jalr() {
        let code = "
            addi a1, zero, 42
            jalr a0, -8(a1)
        ";
        riscv_test!(code,"test_jalr",2,"a0"=>DRAM_BASE+8,"pc"=>34);
    }

    #[test]
    fn test_beq() {
        let code = "
            beq x0, x0, 42
        ";
        riscv_test!(code,"test_beq",3,"pc"=>DRAM_BASE+42);
    }

    #[test]
    fn test_bne() {
        let code = "
            addi x1, x0, 10
            bne x0, x1, 42
        ";
        riscv_test!(code,"test_bne",5,"pc"=>DRAM_BASE+42+4);
    }

    #[test]
    fn test_blt() {
        let code = "
            addi x1, x0, 10
            addi x2, x0, 20
            blt x1,x2,42
        ";
        riscv_test!(code,"test_blt",3,"pc"=>DRAM_BASE+42+8);
    }

    #[test]
    fn test_bge() {
        let code = "
            addi x1,x0,10
            addi x2,x0,20
            bge x2,x1,42
        ";
        riscv_test!(code,"test_bge",3,"pc"=>DRAM_BASE+42+8);
    }

    #[test]
    fn test_bltu(){
        let code = "
            addi x1,x0,10
            addi x2,x0,20
            bltu x1,x2,42
        ";
        riscv_test!(code,"test_bltu",3,"pc"=>DRAM_BASE+42+8);
    }

    #[test]
    fn test_bqeu() {
        let code = "
            addi x1,x0,10
            addi x2,x0,20
            bgeu x2,x1,42
        ";
        riscv_test!(code,"test_bgeu",3,"pc"=>DRAM_BASE+42+8);
    }

    #[test]
    fn test_store_load1() {
        let code = "
            addi s0, zero,256
            addi sp, sp, -16
            sd s0, 8(sp)
            lb t1, 8(sp)
            lh t2, 8(sp)
        ";
        riscv_test!(code,"test_store_load1",10,"t1"=>0,"t2"=>256);
    }

    #[test]
    fn test_slt(){
        let code ="
            addi t0,zero,14
            addi t1,zero,24
            slt t2,t0,t1
            slti t3,t0,42
            sltiu t4,t0,84
        ";
        riscv_test!(code,"test_slt",7,"t2"=>1,"t3"=>1,"t4"=>1);
    }

   
    #[test]
    fn test_xor() {
        let code = "
            addi a0, zero, 0b10
            xori a1, a0, 0b01
            xor a2, a1, a1 
        ";
        riscv_test!(code, "test_xor", 5, "a1" => 3, "a2" => 0);
    }
     #[test]
    fn test_or() {
        let code = "
            addi a0, zero, 0b10
            ori  a1, a0, 0b01
            or   a2, a0, a0
        ";
        riscv_test!(code, "test_or", 3, "a1" => 0b11, "a2" => 0b10);
    }


    #[test]
    fn test_and() {
        let code = "
            addi a0, zero, 0b10
            andi a1, a0, 0b11
            and a2, a0, a1
        ";
        riscv_test!(code,"test_and",3,"a1" => 0b10,"a2" => 0b10);
    }

    #[test]
    fn test_sll() {
            let code = "
            addi a0, zero, 1
            addi a1, zero, 5
            sll  a2, a0, a1
            slli a3, a0, 5
            addi s0, zero, 64
            sll  a4, a0, s0
        ";
        riscv_test!(code, "test_sll", 10, "a2" => 1 << 5, "a3" => 1 << 5, "a4" => 1);
    }

    #[test]
    fn test_sra_srl() {
        let code = "
            addi a0, zero, -8
            addi a1, zero, 1
            sra  a2, a0, a1
            srai a3, a0, 2
            srli a4, a0, 2
            srl  a5, a0, a1
        ";
        riscv_test!(code, "test_sra_srl", 10, "a2" => -4 as i64 as u64, "a3" => -2 as i64 as u64, 
                                              "a4" => -8 as i64 as u64 >> 2, "a5" => -8 as i64 as u64 >> 1);
    }

     #[test]
    fn test_word_op() {
        let code = "
            addi a0, zero, 42 
            lui  a1, 0x7f000
            addw a2, a0, a1
        ";
        riscv_test!(code, "test_word_op", 29, "a2" => 0x7f00002a);
    }

    #[test]
    fn test_csrs1() {
        let code = "
        addi t0, zero, 1
        addi t1, zero, 2
        addi t2, zero, 3
        csrrw zero, mstatus, t0
        csrrs zero, mtvec, t1
        csrrw zero, mepc, t2
        csrrc t2, mepc, zero
        csrrwi zero, sstatus, 4
        csrrsi zero, stvec, 5
        csrrwi zero, sepc, 6
        csrrci zero, sepc, 0 
    ";
    riscv_test!(code, "test_csrs1", 20, "mstatus" => 1, "mtvec" => 2, "mepc" => 3,
                                        "sstatus" => 0, "stvec" => 5, "sepc" => 6);
    }
    #[test]
    fn compile_hello_world() {
        // You should run it by
        // -- cargo run helloworld.bin
        let c_code = r"
        int main() {
            volatile char *uart = (volatile char *) 0x10000000;
            uart[0] = 'H';
            uart[0] = 'e';
            uart[0] = 'l';
            uart[0] = 'l';
            uart[0] = 'o';
            uart[0] = ',';
            uart[0] = ' ';
            uart[0] = 'w';
            uart[0] = 'o';
            uart[0] = 'r';
            uart[0] = 'l';
            uart[0] = 'd';
            uart[0] = '!';
            uart[0] = '\n';
            return 0;
        }";
        let mut file = File::create("test_helloworld.c").unwrap();
        file.write(&c_code.as_bytes()).unwrap();
        generate_rv_assembly("test_helloworld.c");
        generate_rv_obj("test_helloworld.s");
        generate_rv_binary("test_helloworld");
    }
}
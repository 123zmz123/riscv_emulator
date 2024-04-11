#![allow(dead_code)]
use std::mem::size_of;
use crate::bus::*;
use crate::exception::*;
use crate::interrupt::*;
use crate::param::*;
use crate::csr::*;
use crate::virtqueue::*;

type Mode = u64;
const Machine: Mode = 0b11;
const Supervisor: Mode = 0b01;
const User: Mode = 0b00;

pub enum AccessType {
    Instruction,
    Load,
    Store,
}
pub struct Cpu{
    pub pc: u64, // pc point to current instruction address
    pub regs: [u64; 32], // riscv have 32 general registers
    pub mode: Mode,
    pub bus: Bus, // bus is reponsible for access external device
    pub csr: Csr, // csr reg groups
    pub enable_paging: bool, // do we need enable page?
    pub page_table: u64, // point to the page table
}

const RVABI: [&str; 32] = [
     "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", 
    "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5", 
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", 
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6",
];

impl Cpu {
    pub fn new(code: Vec<u8>, disk_image: Vec<u8>) -> Self {
        let mut regs = [0; 32];
        regs[2] = DRAM_END;
        let pc = DRAM_BASE;
        let bus = Bus::new(code, disk_image);
        let csr = Csr::new();
        let mode = Machine;
        let page_table = 0;
        let enable_paging = false;
        Self {regs, pc, bus, csr, mode, page_table, enable_paging}
    }

    // get reg value.
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
    // print out the current pc
    pub fn dump_pc(&self) {
        println!("{:-^80}","PC register");
        println!("PC={:#x}\n",self.pc);
    }
    // when error happened print out current reg status
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
    /// cpu will check whether handle the excepution after each fetch-execute cycle.
    pub fn handle_exception(&mut self, e:Exception){
        let pc = self.pc;
        let mode = self.mode;
        let cause = e.code();
        // by default all exception were handled in M mode, but by mdelegate reg some can hanle in lower privelege
        // mode
        let trap_in_s_mode = mode <= Supervisor && self.csr.is_medelegated(cause);
        let (STATUS, TVEC, CAUSE, TVAL,EPC,MASK_PIE,pie_i,MASK_IE,ie_i,MASK_PP,pp_i) 
            = if trap_in_s_mode {
                self.mode = Supervisor;
                // reference rv64 sstatus define
                (SSTATUS, STVEC, SCAUSE, STVAL, SEPC, MASK_SPIE, 5, MASK_SIE, 1, MASK_SPP, 8) 

            } else {
                self.mode = Machine;
                //reference rv64 msstatus define
                (MSTATUS, MTVEC, MCAUSE, MTVAL, MEPC, MASK_MPIE, 7, MASK_MIE, 3, MASK_MPP, 11)
            };
        // pc = vector table address
        self.pc = self.csr.load(TVEC) & !0b11;
        // record the pc number that encounter the exception
        self.csr.store(EPC, pc);
        self.csr.store(CAUSE, cause);
        // record extra message for exception handle
        self.csr.store(TVAL, e.value());
        let mut status = self.csr.load(STATUS);
        // record current ie statu to previous ie statu
        let ie = (status & MASK_IE) >> ie_i;
        status = (status & !MASK_PIE) | (ie << pie_i);
        // disable global interrupt enable
        status &= !MASK_IE;
        // store previous cpu mode
        status = (status & !MASK_PP) | (mode << pp_i);
        self.csr.store(STATUS, status);
    }

    pub fn handle_interrupt(&mut self, interrupt: Interrupt) {
        // similar to exception
        let pc = self.pc; // store the pc before get into intterrupt
        let mode = self.mode;// store the mode before get into intterupt
        let cause = interrupt.code();

        let trap_in_s_mode = mode <= Supervisor && self.csr.is_midelegated(cause);

        let (STATUS, TVEC, CAUSE, TVAL, EPC, MASK_PIE, pie_i, MASK_IE, ie_i, MASK_PP, pp_i) 
            = if trap_in_s_mode {
                self.mode = Supervisor;
                (SSTATUS, STVEC, SCAUSE, STVAL, SEPC, MASK_SPIE, 5, MASK_SIE, 1, MASK_SPP, 8)
            } else {
                self.mode = Machine;
                (MSTATUS, MTVEC, MCAUSE, MTVAL, MEPC, MASK_MPIE, 7, MASK_MIE, 3, MASK_MPP, 11)
            };
            //
            //
            //
            //
            //
             // vector base address reg
            let tvec = self.csr.load(TVEC);
            let tvec_mode = tvec & 0b11;
            let tvec_base = tvec & !0b11;
            match tvec_mode {
                0 => self.pc = tvec_base,
                1 => self.pc = tvec_base + cause << 2,
                _ => unreachable!(),
            };
            //
            // When a trap is taken into S-mode (or M-mode), sepc (or mepc) is written with the virtual address 
            // of the instruction that was interrupted or that encountered the exception.
            self.csr.store(EPC, pc); // record the pc address which cause the interrupt
            //
            // When a trap is taken into S-mode (or M-mode), scause (or mcause) is written with a code indicating 
            // the event that caused the trap.
            self.csr.store(CAUSE, cause);
            //
            // When a trap is taken into M-mode, mtval is either set to zero or written with exception-specific 
            // information to assist software in handling the trap. 
            self.csr.store(TVAL, 0);
            // prepare for manipulate sstatus or msstatus register
            let mut status = self.csr.load(STATUS);
            // get SIE or MIE value
            let ie = (status & MASK_IE) >> ie_i;
            // set PIE = IE
            status = (status & !MASK_PIE) | (ie << pie_i);
            // IE set to zero
            status &= !MASK_IE;
            // record previous mode 
            status = (status & !MASK_PP) | (mode << pp_i);
            self.csr.store(STATUS, status);
        
    }

    pub fn check_pending_interrupt(&mut self) -> Option<Interrupt>{
        use Interrupt::*;
        // 3.1.6.1
        // When a hart is executing in privilege mode x, interrupts are globally enabled when x IE=1 and globally 
        // disabled when xIE=0. Interrupts for lower-privilege modes, w<x, are always globally disabled regardless 
        // of the setting of any global wIE bit for the lower-privilege mode. Interrupts for higher-privilege modes, 
        // y>x, are always globally enabled regardless of the setting of the global yIE bit for the higher-privilege 
        // mode. Higher-privilege-level code can use separate per-interrupt enable bits to disable selected higher-
        // privilege-mode interrupts before ceding control to a lower-privilege mode
 
        // 3.1.9 & 4.1.3
        // An interrupt i will trap to M-mode (causing the privilege mode to change to M-mode) if all of
        // the following are true: (a) either the current privilege mode is M and the MIE bit in the mstatus
        // register is set, or the current privilege mode has less privilege than M-mode; (b) bit i is set in both
        // mip and mie; and (c) if register mideleg exists, bit i is not set in mideleg.
        if (self.mode == Machine) && (self.csr.load(MSTATUS) & MASK_MIE) == 0 {
            return None;
        }
        if (self.mode == Supervisor) && (self.csr.load(SSTATUS) & MASK_SIE) == 0 {
            return None;
        }
        
        // In fact, we should using priority to decide which interrupt should be handled first.
        if self.bus.uart.is_interrupted() {
            self.bus.store(PLIC_SCLAIM, 32, UART_IRQ).unwrap();
            self.csr.store(MIP, self.csr.load(MIP) | MASK_SEIP); 
        } else if self.bus.virtio_blk.is_interrupted() {
            self.disk_access();
            self.bus.store(PLIC_SCLAIM, 32, VIRTIO_IRQ).unwrap();
            self.csr.store(MIP, self.csr.load(MIP) | MASK_SEIP);
        }
        // 3.1.9 & 4.1.3
        // Multiple simultaneous interrupts destined for M-mode are handled in the following decreasing
        // priority order: MEI, MSI, MTI, SEI, SSI, STI.
        let pending = self.csr.load(MIE) & self.csr.load(MIP);
        /// check the pending reason and return the interrupt type
        if (pending & MASK_MEIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_MEIP);
            return Some(MachineExternalInterrupt);
        }
        if (pending & MASK_MSIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_MSIP);
            return Some(MachineSoftwareInterrupt);
        }
        if (pending & MASK_MTIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_MTIP);
            return Some(MachineTimerInterrupt);
        }
        if (pending & MASK_SEIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_SEIP);
            return Some(SupervisorExternalInterrupt);
        }
        if (pending & MASK_SSIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_SSIP);
            return Some(SupervisorSoftwareInterrupt);
        }
        if (pending & MASK_STIP) != 0 {
            self.csr.store(MIP, self.csr.load(MIP) & !MASK_STIP);
            return Some(SupervisorTimerInterrupt);
        }
        return None;
    }
    pub fn disk_access(&mut self) {
        const desc_size: u64 = size_of::<VirtqDesc>() as u64;
        // 2.6.2 Legacy Interfaces: A Note on Virtqueue Layout
        // ------------------------------------------------------------------
        // Descriptor Table  | Available Ring | (...padding...) | Used Ring
        // ------------------------------------------------------------------
        let desc_addr = self.bus.virtio_blk.desc_addr();
        let avail_addr = desc_addr + DESC_NUM as u64 * desc_size;
        let used_addr = desc_addr + PAGE_SIZE;

        // cast addr to a reference to ease field access.
        let virtq_avail = unsafe { &(*(avail_addr as *const VirtqAvail)) };
        let virtq_used  = unsafe { &(*(used_addr  as *const VirtqUsed)) };

        // The idx field of virtq_avail should be indexed into available ring to get the
        // index of descriptor we need to process.
        let idx = self.bus.load(&virtq_avail.idx as *const _ as u64, 16).unwrap() as usize;
        let index = self.bus.load(&virtq_avail.ring[idx % DESC_NUM] as *const _ as u64, 16).unwrap();

        // The first descriptor:
        // which contains the request information and a pointer to the data descriptor.
        let desc_addr0 = desc_addr + desc_size * index;
        let virtq_desc0 = unsafe { &(*(desc_addr0 as *const VirtqDesc)) };
        // The addr field points to a virtio block request. We need the sector number stored 
        // in the sector field. The iotype tells us whether to read or write.
        let req_addr = self.bus.load(&virtq_desc0.addr as *const _ as u64, 64).unwrap();
        let virtq_blk_req = unsafe { &(*(req_addr as *const VirtioBlkRequest)) };
        let blk_sector = self.bus.load(&virtq_blk_req.sector as *const _ as u64, 64).unwrap();
        let iotype = self.bus.load(&virtq_blk_req.iotype as *const _ as u64, 32).unwrap() as u32;
        // The next field points to the second descriptor. (data descriptor)
        let next0  = self.bus.load(&virtq_desc0.next  as *const _ as u64, 16).unwrap();

        // the second descriptor. 
        let desc_addr1 = desc_addr + desc_size * next0;
        let virtq_desc1 = unsafe { &(*(desc_addr1 as *const VirtqDesc)) };
        // The addr field points to the data to read or write
        let addr1  = self.bus.load(&virtq_desc1.addr  as *const _ as u64, 64).unwrap();
        // the len donates the size of the data
        let len1   = self.bus.load(&virtq_desc1.len   as *const _ as u64, 32).unwrap();
        // the flags mark this buffer as device write-only or read-only.
        // We ignore it here
        // let flags1 = self.bus.load(&virtq_desc1.flags as *const _ as u64, 16).unwrap();
        match iotype {
            VIRTIO_BLK_T_OUT => {
                for i in 0..len1 {
                    let data = self.bus.load(addr1 + i, 8).unwrap();
                    self.bus.virtio_blk.write_disk(blk_sector * SECTOR_SIZE + i, data);
                }
            }
            VIRTIO_BLK_T_IN => {
                for i in 0..len1 {
                    let data = self.bus.virtio_blk.read_disk(blk_sector * SECTOR_SIZE + i);
                    self.bus.store(addr1 + i, 8, data as u64).unwrap();
                }
            } 
            _ => unreachable!(),
        }       

        let new_id = self.bus.virtio_blk.get_new_id();
        self.bus.store(&virtq_used.idx as *const _ as u64, 16, new_id % 8).unwrap();
    }

    fn update_paging(&mut self, csr_addr: usize){
        // satp is control register of virtual address feature
        if csr_addr != SATP { return; }
        let satp = self.csr.load(SATP);
        // calculate the page table address algorithm provide by arch mannual
        self.page_table = (satp & MASK_PPN) * PAGE_SIZE;  
        // focus on stap 0bxxx..... highest 4 bit
        let mode = satp >> 60; 
        self.enable_paging = mode == 8;
    }

    /// Translate a virtual address to a physical address for the paged virtual-dram system.
    pub fn translate(&mut self, addr:u64, access_type:AccessType) -> Result<u64,Exception> {
        if !self.enable_paging {
            return Ok(addr);
        }

        let levels = 3;
        // sv39 va_addres -> index of each level PTE + offset
        let vpn = [
            (addr >> 12) & 0x1ff,
            (addr >> 21) & 0x1ff,
            (addr >> 30) & 0x1ff,
        ];
        //1. Let a be satp.ppn × PAGESIZE, and let i = LEVELS − 1.
        let mut a = self.page_table;
        let mut i: i64 = levels - 1;
        let mut pte;
        
        loop {
            // "2. Let pte be the value of the PTE at address a+va.vpn[i]×PTESIZE. (For Sv39,
            //     PTESIZE=8.) If accessing pte violates a PMA or PMP check, raise an access
            //     exception corresponding to the original access type."
            pte = self.bus.load(a + vpn[i as usize] * 8, 64)?;

            // "3. If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise a page-fault
            //     exception corresponding to the original access type."
            let v = pte & 1;
            let r = (pte >> 1) & 1;
            let w = (pte >> 2) & 1;
            let x = (pte >> 3) & 1;
            if v == 0 || (r == 0 && w == 1) {
                match access_type {
                    AccessType::Instruction => return Err(Exception::InstructionPageFault(addr)),
                    AccessType::Load => return Err(Exception::LoadPageFault(addr)),
                    AccessType::Store => return Err(Exception::StoreAMOPageFault(addr)),
                }
            }

            // "4. Otherwise, the PTE is valid. If pte.r = 1 or pte.x = 1, go to step 5.
            //     Otherwise, this PTE is a pointer to the next level of the page table.
            //     Let i = i − 1. If i < 0, stop and raise a page-fault exception
            //     corresponding to the original access type. Otherwise,
            //     let a = pte.ppn × PAGESIZE and go to step 2."
            if r == 1 || x == 1 {
                break;
            }
            i -= 1;
            // pte = |ppn|flags|
            let ppn = (pte >> 10) & 0x0fff_ffff_ffff;
            // accoring ppn recalculate next level pte table address.
            a = ppn * PAGE_SIZE;
            if i < 0 {
                match access_type {
                    AccessType::Instruction => return Err(Exception::InstructionPageFault(addr)),
                    AccessType::Load => return Err(Exception::LoadPageFault(addr)),
                    AccessType::Store => return Err(Exception::StoreAMOPageFault(addr)),
                }
            }
        }

        // A leaf PTE has been found.
        let ppn = [
            (pte >> 10) & 0x1ff,
            (pte >> 19) & 0x1ff,
            (pte >> 28) & 0x03ff_ffff,
        ];

        // We skip implementing from step 5 to 7.

        // "5. A leaf PTE has been found. Determine if the requested dram access is allowed by
        //     the pte.r, pte.w, pte.x, and pte.u bits, given the current privilege mode and the
        //     value of the SUM and MXR fields of the mstatus register. If not, stop and raise a
        //     page-fault exception corresponding to the original access type."

        // "6. If i > 0 and pte.ppn[i − 1 : 0] ̸= 0, this is a misaligned superpage; stop and
        //     raise a page-fault exception corresponding to the original access type."

        // "7. If pte.a = 0, or if the dram access is a store and pte.d = 0, either raise a
        //     page-fault exception corresponding to the original access type, or:
        //     • Set pte.a to 1 and, if the dram access is a store, also set pte.d to 1.
        //     • If this access violates a PMA or PMP check, raise an access exception
        //     corresponding to the original access type.
        //     • This update and the loading of pte in step 2 must be atomic; in particular, no
        //     intervening store to the PTE may be perceived to have occurred in-between."

        // "8. The translation is successful. The translated physical address is given as
        //     follows:
        //     • pa.pgoff = va.pgoff.
        //     • If i > 0, then this is a superpage translation and pa.ppn[i−1:0] =
        //     va.vpn[i−1:0].
        //     • pa.ppn[LEVELS−1:i] = pte.ppn[LEVELS−1:i]."
        let offset = addr & 0xfff;
        match i {
            0 => {
                let ppn = (pte >> 10) & 0x0fff_ffff_ffff;
                Ok((ppn << 12) | offset)
            }
            1 => {
                // Superpage translation. A superpage is a dram page of larger size than an
                // ordinary page (4 KiB). It reduces TLB misses and improves performance.
                Ok((ppn[2] << 30) | (ppn[1] << 21) | (vpn[0] << 12) | offset)
            }
            2 => {
                // Superpage translation. A superpage is a dram page of larger size than an
                // ordinary page (4 KiB). It reduces TLB misses and improves performance.
                Ok((ppn[2] << 30) | (vpn[1] << 21) | (vpn[0] << 12) | offset)
            }
            _ => match access_type {
                AccessType::Instruction => return Err(Exception::InstructionPageFault(addr)),
                AccessType::Load => return Err(Exception::LoadPageFault(addr)),
                AccessType::Store => return Err(Exception::StoreAMOPageFault(addr)),
            },
        }
    }
    
    pub fn load(&mut self, addr: u64, size: u64) -> Result<u64, Exception> {
        // according page table on/off statu , calculate the real address we need handle
        let p_addr = self.translate(addr, AccessType::Load)?;
        self.bus.load(p_addr, size)
    }

    pub fn store(&mut self, addr:u64, size: u64, value: u64)->Result<(), Exception>{
        // according page table on/off statu , calculate the real address we need handle
        let p_addr = self.translate(addr,AccessType::Store)?;
        self.bus.store(p_addr, size, value)
    }

    pub fn fetch(&mut self)->Result<u64,Exception>{
        // according page table on/off statu , calculate the real address we need handle
        let p_pc = self.translate(self.pc, AccessType::Instruction)?;
        match self.bus.load(p_pc, 32) {
            Ok(instr) => Ok(instr),
            Err(_e) => Err(Exception::InstructionAccessFault(self.pc)),
        }
    }
    #[inline]
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
                // 1. addr = rs1.val + imm
                // 2. rd.val = memory[addr]
                let imm = ((instr as i32 as i64) >> 20) as u64;
                let addr = self.regs[rs1].wrapping_add(imm);
                match funct3 {
                    0x0 => {
                        // lb rd, imm(rs1)
                        let val = self.load(addr, 8)?;
                        self.regs[rd] = val as i8 as i64 as u64;
                        return self.update_pc();
                    }

                    0x1 => {
                        // lh rd, imm(rs1)
                        let val = self.load(addr, 16)?;
                        self.regs[rd] = val as i16 as i64 as u64;
                        return self.update_pc();
                    }

                    0x2 => {
                        // lw rd, imm(rs1)
                        let val = self.load(addr, 32)?;
                        self.regs[rd] = val as i32 as i64 as u64;
                        return self.update_pc();
                    }

                    0x3 => {
                        // ld rd, imm(rs1)
                        let val = self.load(addr, 64)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x4 => {
                        // lbu rd, imm(rs1)
                        let val = self.load(addr, 8)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x5 => {
                        // lhu rd, imm(rs1)
                        let val = self.load(addr, 16)?;
                        self.regs[rd] = val;
                        return self.update_pc();
                    }

                    0x6 => {
                        // lwu rd, imm(rs1)
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
                        // addi rd, rs1, imm
                        // rd = rs1 + imm
                        self.regs[rd] = self.regs[rs1].wrapping_add(imm);
                        return self.update_pc();
                    }

                    0x1 => {
                        // slli rd, rs1, shamt
                        // rd = rs1 << shamt
                        self.regs[rd] = self.regs[rs1] << shamt;
                        return self.update_pc();
                    }

                    0x2 => {
                        // slti rd, rs1, imm
                        // rd = 1 if rs1 < imm else = 0
                        self.regs[rd] = if (self.regs[rs1] as i64) < (imm as i64) { 1 } else { 0 };
                        return self.update_pc();
                    }

                    0x3 => {
                        // sltiu rd, rs1, imm
                        self.regs[rd] = if self.regs[rs1] < imm { 1 } else { 0 };
                        return self.update_pc();
                    }

                    0x4 => {
                        //xori rd , rs1, imm
                        // rd = rs1 ^ imm
                        self.regs[rd] = self.regs[rs1]^imm;
                        return self.update_pc();
                    }
                    0x5 => {
                        match funct7 >> 1 {
                            //srli rd, rs1,shamt
                            // rd =  rs1 >> shamt
                            0x00 => {
                                self.regs[rd] = self.regs[rs1].wrapping_shr(shamt);
                                return self.update_pc();
                            }

                            //srai rd, rs1, shamt
                            // rd = rs1 >> shamt, val as i64
                            0x10 => {
                                self.regs[rd]=(self.regs[rs1] as i64).wrapping_shr(shamt) as u64;
                                return self.update_pc();
                            }
                            _ => Err(Exception::IllegalInstruction(instr)),
                            
                        }
                    }

                    0x6 => {
                        //ori rd, rs1, imm
                        // rd = rs1 | imm
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
                //rd = pc + imm
                let imm = (instr & 0xfffff000) as i32 as i64 as u64;
                self.regs[rd] = self.pc.wrapping_add(imm);
                return self.update_pc();
            }

            0x1b => { //
                let imm = ((instr as i32 as i64)>>20) as u64;
                let shamt = (imm & 0x1f) as u32;
                match funct3 {
                    0x0 => {
                        //addiw rd, rs1, imm
                        // rd = rs1+imm
                        self.regs[rd]=self.regs[rs1].wrapping_add(imm) as i32 as i64 as u64;
                        return self.update_pc();
                    }
                    0x1 => {
                        //slliw
                        // rd = rs1 << shamt
                        self.regs[rd] = self.regs[rs1].wrapping_shl(shamt) as i32 as i64 as u64;
                        return self.update_pc();
                    }
                    0x5 => {
                        match funct7 {
                            0x00 => {
                                //srliw
                                // rd = rs1 >> shamt
                                self.regs[rd] = (self.regs[rs1] as u32).wrapping_shr(shamt) as i32
                                    as i64 as u64;
                                return self.update_pc();
                            }
                            0x20 => {
                                // sraiw
                                // rd = rs1 >> shamt
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
                    0x0 => {self.store(addr,8,self.regs[rs2])?;self.update_pc()},//sb mem[addr]=rs2
                    0x1 => {self.store(addr,16,self.regs[rs2])?;self.update_pc()},//sh mem[addr]=rs2
                    0x2 => {self.store(addr,32,self.regs[rs2])?;self.update_pc()},//sw mem[addr]=rs2
                    0x3 => {self.store(addr,64,self.regs[rs2])?;self.update_pc()},//sd mem[addr]=rs2
                    _ => unreachable!(),
                }
            }
            // memory atomic operation
            0x2f => { // atomic function which means all the operation happen at a single time unit
                let funct5 = (funct7 & 0b1111100) >> 2;
                let _aq = (funct7 & 0b0000010) >> 1;
                let _rl = funct7 & 0b0000001;
                match (funct3,funct5) {
                    (0x2,0x00)=>{
                        // amoadd.w
                        // t=mem[rs1], mem[rs1]=t+rs2, rd=t
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
                        // rd = rs1 + rs2
                        self.regs[rd] = self.regs[rs1].wrapping_add(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x0, 0x01) => {
                        // mul
                        // rd = rs1*rs2
                        self.regs[rd] = self.regs[rs1].wrapping_mul(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x0, 0x20) => {
                        // sub
                        // rd = rs1 - rs2
                        self.regs[rd]=self.regs[rs1].wrapping_sub(self.regs[rs2]);
                        return self.update_pc();
                    }

                    (0x1, 0x00) => {
                        // sll 
                        //rd = rs1 << shamt
                        self.regs[rd]=self.regs[rs1].wrapping_shl(shamt);
                        return self.update_pc();
                    }

                    (0x2, 0x00) => {
                        // slt
                        // rd = 1 if rs1 < rs2 else = 0
                        self.regs[rd] = if (self.regs[rs1] as i64) < (self.regs[rs2] as i64) { 1 } else { 0 };
                        return self.update_pc();
                    }

                    (0x3, 0x00) => {
                        // sltu
                        // rd = 1 if rs1 < rs2 else = 0
                        self.regs[rd] = if self.regs[rs1] < self.regs[rs2] { 1 } else { 0 };
                        return self.update_pc();
                    }

                    (0x4, 0x00) => {
                        // xor
                        // rd = rs1 ^ rs2
                        self.regs[rd] = self.regs[rs1]^self.regs[rs2];
                        return self.update_pc();
                    }

                    (0x5, 0x00) => {
                        // srl
                        // rd = rs1 >> shamt
                        self.regs[rd] = self.regs[rs1].wrapping_shr(shamt);
                        return self.update_pc();
                    }

                    (0x5, 0x20) => {
                        // sra
                        // rd = rs1 >> shamt
                        self.regs[rd] = (self.regs[rs1] as i64).wrapping_shr(shamt) as u64;
                        return self.update_pc();
                    }

                    (0x6, 0x00) => {
                        // or
                        // rd = rs1 | rs2
                        self.regs[rd] = self.regs[rs1] | self.regs[rs2];
                        return self.update_pc();
                    }

                    (0x7, 0x00) => {
                        // and
                        // rd = rs1 & rs2
                        self.regs[rd] = self.regs[rs1] & self.regs[rs2];
                        return self.update_pc();
                    }

                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }   
            
            0x37 => {
                // lui load imm upper bound to rd
                // rd = imm's upper bound
                self.regs[rd] = (instr & 0xfffff000) as i32 as i64 as u64;
                return self.update_pc();
            }

            0x3b => {
                let shamt = (self.regs[rs2] & 0x1f) as u32;
                match (funct3, funct7) {
                    (0x0, 0x00) => {
                        // addw
                        // rd = rs1 + rs2
                        self.regs[rd] =
                            self.regs[rs1].wrapping_add(self.regs[rs2]) as i32 as i64 as u64;
                        return self.update_pc();
                        
                    }

                    (0x0, 0x20) => {
                        // subw
                        // rd = rs1 - rs2
                        self.regs[rd] = 
                            ((self.regs[rs1].wrapping_sub(self.regs[rs2])) as i32) as u64;
                        return self.update_pc();
                    }

                    (0x1, 0x00) => {
                        // sllw
                        // rd = rs1 << shamt
                        self.regs[rd] = (self.regs[rs1] as u32).wrapping_shl(shamt) as i32 as u64;
                        return self.update_pc();
                    }

                    (0x5, 0x00) => {
                        // srlw
                        // rd = rs1 >> shamr
                        self.regs[rd] = (self.regs[rs1] as u32).wrapping_shr(shamt) as i32 as u64;
                        return self.update_pc();
                    }
                    (0x5,0x01) => {
                        // divu
                        // rd =  rs1 / rs2 if rs2 != 0 else =0
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
                        // rd = rs1 >> shamt
                        self.regs[rd] = ((self.regs[rs1] as i32) >> (shamt as i32)) as u64;
                        return self.update_pc();
                    }
                    (0x7,0x01) => {
                        // remuw
                        // rd =  rs1 / rs2 if rs2 != 0 else =0
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
                        // if rs1 == rs2 then pc = pc + imm
                        if self.regs[rs1] == self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x1 => {
                        // bne
                        // if rs1!=rs2 then pc=pc+imm
                        if self.regs[rs1] != self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x4 => {
                        // blt
                        // if rs1 < rs2 then pc=pc+imm
                        if (self.regs[rs1] as i64) < (self.regs[rs2] as i64) {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x5 => {
                        // bge
                        // if rs1 >= rs2 then pc=pc+imm
                        if (self.regs[rs1] as i64) >= (self.regs[rs2] as i64) {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x6 => {
                        // bltu
                        // if rs1 < rs2 then pc=pc+imm
                        if self.regs[rs1] < self.regs[rs2] {
                            return Ok(self.pc.wrapping_add(imm));
                        }
                        return self.update_pc();
                    }

                    0x7 => {
                        // bgeu
                        // if rs1 >= rs2 then pc=pc+imm
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
                // rd = previous pc, new pc = (rs1+imm)& 0b111..10
                let t = self.pc + 4;
                let imm = ((((instr & 0xfff00000) as i32) as i64) >> 20) as u64;
                let new_pc = (self.regs[rs1].wrapping_add(imm)) & !1;

                self.regs[rd] = t;
                return Ok(new_pc);
            }

            0x6f => {
                // jal
                // rd = previous pc, new_pc = rs1 + imm
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
                        // csr_reg = rs1
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,self.regs[rs1]);
                        self.regs[rd] = t;
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }

                    0x2 => {
                        // csrrs
                        // rd = csr_reg
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr, t | self.regs[rs1]);
                        self.regs[rd]=t;
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }

                    0x3 => {
                        // csrrc
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,t&(!self.regs[rs1]));
                        self.regs[rd]=t;
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }

                    0x5 => {
                        // csrrwi
                        let zimm = rs1 as u64;
                        self.regs[rd]=self.csr.load(csr_addr);
                        self.csr.store(csr_addr,zimm);
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }

                    0x6 => {
                        //csrrsi
                        let zimm = rs1 as u64;
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr, t|zimm);
                        self.regs[rd]=t;
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }

                    0x7 => {
                        //csrrci
                        let zimm = rs1 as u64;
                        let t = self.csr.load(csr_addr);
                        self.csr.store(csr_addr,t & (!zimm));
                        self.regs[rd]=t;
                        self.update_paging(csr_addr);
                        return self.update_pc();
                    }
                    
                    _ => Err(Exception::IllegalInstruction(instr)),
                }
            }
            _ => Err(Exception::IllegalInstruction(instr)),
        }
    }
}


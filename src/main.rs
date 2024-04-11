mod param;
mod dram;
mod bus;
mod cpu;
mod exception;
mod csr;
mod plic;
mod clint;
mod uart;
mod interrupt;
mod virtqueue;
mod virtio;


use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;

use crate::cpu::*;

// cmd:    riscv_emulator xv6-kernel.bin xv6-fs.img
fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();

    if (args.len() != 2) && (args.len() != 3) {
        panic!("Usage: execute_file xv6-kernel.bin xv6-fs.img");
    }
    let mut file = File::open(&args[1])?;
    let mut binary = Vec::new();
    file.read_to_end(&mut binary)?;

    let mut disk_image = Vec::new();
    if args.len() == 3 { // fs img file
        let mut file = File::open(&args[2])?;
        file.read_to_end(&mut disk_image)?;
    }

    let mut cpu = Cpu::new(binary, disk_image); // load code to dram

    loop {
        let inst = match cpu.fetch() { //fetch a instruction
            // fetch the instruction out
            Ok(inst) => inst,
            // handle fetch related exception 
            Err(e) => {
                cpu.handle_exception(e);
                if e.is_fatal() {
                    println!("{}", e);
                    break;
                }
                continue;
            }
        };

        match cpu.execute(inst) {
            // execute one command and get next command address
            Ok(new_pc) => cpu.pc = new_pc,
            Err(e) => {
                cpu.handle_exception(e);
                if e.is_fatal() {
                    println!("{}", e);
                    break;
                }
            }
        };
        // check if we should handle the interrupt
        match cpu.check_pending_interrupt() {
            Some(interrupt) => cpu.handle_interrupt(interrupt),
            None => (),
        }

    }
    // once terminated then print the current cpu status
    cpu.dump_registers();
    cpu.dump_csrs();
    cpu.dump_pc();

    Ok(())
}
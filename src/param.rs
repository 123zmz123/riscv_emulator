pub const DRAM_BASE:u64 = 0x8000_0000;
pub const DRAM_SIZE:u64 = 1024*1024*128;
pub const DRAM_END:u64 = DRAM_BASE+DRAM_SIZE-1;


pub const CLINT_BASE :u64 = 0x200_0000;
pub const CLINT_SIZE: u64 = 0x10000;
pub const CLINT_END: u64 = CLINT_BASE + CLINT_SIZE -1;

pub const CLINT_MTIMECMP: u64 = CLINT_BASE + 0x4000;
pub const CLINT_MTIME: u64 = CLINT_BASE + 0xbff8;


pub const PLIC_BASE: u64 = 0xc00_0000;
pub const PLIC_SIZE: u64 = 0x4000000;
pub const PLIC_END: u64 = PLIC_BASE + PLIC_SIZE -1;

pub const PLIC_PENDING: u64 = PLIC_BASE + 0x1000;
pub const PLIC_SENABLE: u64 = PLIC_BASE + 0x2000;
pub const PLIC_SPRIORITY: u64 = PLIC_BASE + 0x201000;
pub const PLIC_SCLAIM: u64 = PLIC_BASE + 0x201004;

// UART
pub const UART_BASE: u64 = 0x1000_0000;
pub const UART_SIZE: u64 = 0x100;
pub const UART_END: u64 = UART_BASE+UART_SIZE-1;
// uart interrupt request
pub const UART_IRQ: u64 = 10;
// receive holding register
pub const UART_RHR: u64 = 0;
// send holding register
pub const UART_THR: u64 = 0;
//
pub const UART_LCR: u64 = 3;

pub const  UART_LSR: u64 = 5;

pub const MASK_UART_LSR_RX: u8 = 1;

pub const MASK_UART_LSR_TX:u8 = 1<<5;

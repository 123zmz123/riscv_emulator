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

// VIRTIO
// The virtio spec:
// https://docs.oasis-open.org/virtio/virtio/v1.1/virtio-v1.1.pdf

// The address which virtio starts.
pub const VIRTIO_BASE: u64 = 0x1000_1000;
// The size of virtio.
pub const VIRTIO_SIZE: u64 = 0x1000;
// The interrupt request of virtio.
pub const VIRTIO_END: u64 = VIRTIO_BASE + VIRTIO_SIZE - 1;
pub const VIRTIO_IRQ: u64 = 1;

// The number of virtio descriptors. It must be a power of two.
pub const DESC_NUM: usize = 8;

// Always return 0x74726976.
pub const VIRTIO_MAGIC: u64 = VIRTIO_BASE + 0x000;
// The version. 1 is legacy.
pub const VIRTIO_VERSION: u64 = VIRTIO_BASE + 0x004;
// device type; 1 is net, 2 is disk.
pub const VIRTIO_DEVICE_ID: u64 = VIRTIO_BASE + 0x008;
// Always return 0x554d4551
pub const VIRTIO_VENDOR_ID: u64 = VIRTIO_BASE + 0x00c;
// Device features.
pub const VIRTIO_DEVICE_FEATURES: u64 = VIRTIO_BASE + 0x010;
// Driver features.
pub const VIRTIO_DRIVER_FEATURES: u64 = VIRTIO_BASE + 0x020;
// Page size for PFN, write-only.
pub const VIRTIO_GUEST_PAGE_SIZE: u64 = VIRTIO_BASE + 0x028;
// Select queue, write-only.
pub const VIRTIO_QUEUE_SEL: u64 = VIRTIO_BASE + 0x030;
// Max size of current queue, read-only. In QEMU, `VIRTIO_COUNT = 8`.
pub const VIRTIO_QUEUE_NUM_MAX: u64 = VIRTIO_BASE + 0x034;
// Size of current queue, write-only.
pub const VIRTIO_QUEUE_NUM: u64 = VIRTIO_BASE + 0x038;
// Physical page number for queue, read and write.
pub const VIRTIO_QUEUE_PFN: u64 = VIRTIO_BASE + 0x040;
// Notify the queue number, write-only.
pub const VIRTIO_QUEUE_NOTIFY: u64 = VIRTIO_BASE + 0x050;
// Device status, read and write. Reading from this register returns the current device status flags.
// Writing non-zero values to this register sets the status flags, indicating the OS/driver
// progress. Writing zero (0x0) to this register triggers a device reset.
pub const VIRTIO_STATUS: u64 = VIRTIO_BASE + 0x070;


pub const PAGE_SIZE: u64 = 4096;
pub const SECTOR_SIZE: u64 = 512;


// virtio block request type
pub const VIRTIO_BLK_T_IN: u32 = 0;
pub const VIRTIO_BLK_T_OUT: u32 = 1;

// virtqueue descriptor flags
pub const VIRTQ_DESC_F_NEXT: u16 = 1;
pub const VIRTQ_DESC_F_WRITE: u16 = 2;
pub const VIRTQ_DESC_F_INDIRECT: u16 = 4;

pub const PTESIZE:u64 = 8;
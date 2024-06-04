use crate::cpu::{Cpu, Memory};
use crate::instructions::INST_TABLE;

mod disassembler;
mod instructions;
mod cpu;
mod assembler;

fn main() {
    let mut cpu = Cpu::init(0x400);
    let mut mem = Memory::from_file("6502_functional_test.bin");
    cpu.run(&mut mem);
}
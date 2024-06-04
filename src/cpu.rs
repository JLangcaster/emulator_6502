use std::cmp::PartialEq;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter, Write};
use std::ops::Rem;
use std::thread::current;
use crate::instructions::{AddrMode, INST_TABLE, Instruction, Opcode, Operand};

pub struct Memory {
    data: Vec<u8>
}

impl Memory {
    pub fn from_file(path: impl AsRef<std::path::Path>) -> Self {
        return Self {
            data: std::fs::read(path).expect("Couldn't open file"),
        }
    }
}

#[derive(Copy, Clone)]
pub struct StatusRegister(u8);

const FLAG_N: u8 = 0b1000_0000;
const FLAG_V: u8 = 0b0100_0000;
const FLAG_B: u8 = 0b0001_0000;
const FLAG_D: u8 = 0b0000_1000;
const FLAG_I: u8 = 0b0000_0100;
const FLAG_Z: u8 = 0b0000_0010;
const FLAG_C: u8 = 0b0000_0001;

impl Debug for StatusRegister {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("Val: {:02X}, N: {}, V: {}, B: {}, D: {}, I: {}, Z: {}, C: {}",
                                 self.0,
                                 (self.0 & FLAG_N) >> 7,
                                 (self.0 & FLAG_V) >> 6,
                                 (self.0 & FLAG_B) >> 4,
                                 (self.0 & FLAG_D) >> 3,
                                 (self.0 & FLAG_I) >> 2,
                                 (self.0 & FLAG_Z) >> 1,
                                 self.0 & FLAG_C,
        ))
    }
}

impl StatusRegister {
    pub fn init() -> Self {
        return Self(0)
    }

    pub fn get(&self, flag: u8) -> bool {
        return (self.0 & flag) != 0
    }

    pub fn enable(&mut self, flag: u8) {
        self.0 = self.0 | flag
    }

    pub fn disable(&mut self, flag: u8) {
        self.0 = self.0 & !flag
    }

    pub fn flip(&mut self, flag: u8) {
        self.0 = self.0 ^ flag
    }

    pub fn set(&mut self, flag: u8, value: bool) {
        if value {
            self.enable(flag);
        } else {
            self.disable(flag);
        }
    }
}

#[derive(Debug)]
pub enum CpuError {
    IllegalInstruction,
    UnimplementedInstruction,
    IncompatibleAddrMode,
    TrapDetected(Instruction),
}

const ROLLBACK_LENGTH: usize = 10;

pub struct Cpu {
    pub pc: u16,
    pub ac: u8,
    pub x: u8,
    pub y: u8,
    pub sr: StatusRegister,
    pub sp: u8,
    pub previous_instructions: VecDeque<(u16, Instruction)>,
    pub cycles: usize,
}

struct CpuState {
    pc: u16,
    ac: u8,
    x: u8,
    y: u8,
    sr: StatusRegister,
    sp: u8,
    cycles: usize
}

impl Debug for Cpu {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("PC: {:04X}, AC: {:02X}, X: {:02X}, Y: {:02X}, SP: {:02X}, SR:[{:?}]",
        self.pc,
        self.ac,
        self.x,
        self.y,
        self.sp,
        self.sr))
    }
}

impl Display for Cpu {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self))
    }
}

impl Cpu {
    pub fn init(init_pc: u16) -> Self {
        return Self {
            pc: init_pc,
            ac: 0,
            x: 0,
            y: 0,
            sr: StatusRegister(0),
            sp: 0,
            previous_instructions: VecDeque::new(),
            cycles: 0
        }
    }

    fn get_state(&self) -> CpuState {
        return CpuState{
            pc: self.pc,
            ac: self.ac,
            x: self.x,
            y: self.y,
            sr: self.sr,
            sp: self.sp,
            cycles: self.cycles,
        }
    }

    pub fn read_byte(&mut self, mem: &Memory, address: u16) -> u8 {
        self.cycles += 1;
        let val = mem.data[address as usize];

        #[cfg(debug_assertions)]
        println!("Read {:02X} from {:04X}", val, address);

        return val
    }

    pub fn fetch_byte(&mut self, mem: &Memory) -> u8 {
        let byte = self.read_byte(mem, self.pc);
        self.pc = self.pc.wrapping_add(1);
        return byte
    }

    pub fn write_byte(&mut self, mem: &mut Memory, address: u16, byte: u8) {
        self.cycles += 1;
        mem.data[address as usize] = byte;

        #[cfg(debug_assertions)]
        println!("Wrote {:02X} to {:04X}", byte, address);
    }

    pub fn read_word(&mut self, mem: &Memory, address: u16) -> u16 {
        let word_lo = self.read_byte(mem, address);
        let word_hi = self.read_byte(mem, address.wrapping_add(1));
        return u16::from_le_bytes([word_lo, word_hi])
    }

    pub fn fetch_word(&mut self, mem: &Memory) -> u16 {
        let word_lo = self.fetch_byte(mem);
        let word_hi = self.fetch_byte(mem);
        return u16::from_le_bytes([word_lo, word_hi]);
    }

    pub fn write_word(&mut self, mem: &mut Memory, address: u16, word: u16) {
        let [word_lo, word_hi] = word.to_le_bytes();
        self.write_byte(mem, address, word_lo);
        self.write_byte(mem, address.wrapping_add(1), word_hi);
    }

    fn push_instruction_to_rollback(&mut self, pc: u16, instruction: Instruction) {
        self.previous_instructions.push_back((pc, instruction));
        while self.previous_instructions.len() > ROLLBACK_LENGTH {
            self.previous_instructions.pop_front();
        }
    }

    pub fn fetch_instruction(&mut self, mem: &Memory) -> Result<Instruction, CpuError> {
        let current_pc = self.pc;
        let next_opcode_byte = self.fetch_byte(mem);

        let (opcode, addr_mode) = INST_TABLE[next_opcode_byte as usize];
        let operand = match addr_mode {
            AddrMode::Abs => Operand::Abs(self.fetch_word(mem)),
            AddrMode::AbsX => Operand::AbsX(self.fetch_word(mem)),
            AddrMode::AbsY => Operand::AbsY(self.fetch_word(mem)),
            AddrMode::Imm => Operand::Imm(self.fetch_byte(mem)),
            AddrMode::Impl => Operand::Impl,
            AddrMode::Ind => Operand::Ind(self.fetch_word(mem)),
            AddrMode::XInd => Operand::XInd(self.fetch_byte(mem)),
            AddrMode::IndY => Operand::IndY(self.fetch_byte(mem)),
            AddrMode::Rel => Operand::Rel(i8::from_le_bytes([self.fetch_byte(mem)])),
            AddrMode::Zpg => Operand::Zpg(self.fetch_byte(mem)),
            AddrMode::ZpgX => Operand::ZpgX(self.fetch_byte(mem)),
            AddrMode::ZpgY => Operand::ZpgY(self.fetch_byte(mem)),
        };

        let instruction = Instruction::new(opcode, operand, next_opcode_byte);
        self.push_instruction_to_rollback(current_pc, instruction);
        if self.previous_instructions.len() > 1 && (current_pc, instruction) == self.previous_instructions[self.previous_instructions.len() - 2] {
            return Err(CpuError::TrapDetected(instruction))
        }

        return Ok(instruction)
    }

    pub fn execute_instruction(&mut self, mem: &mut Memory, instruction: Instruction) -> Option<CpuError> {
        let result = match (instruction.opcode(), instruction.operand()) {
            (Opcode::ADC, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::Imm(v)) => {self.adc(v); None},
            (Opcode::ADC, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.adc(value); None},
            (Opcode::ADC, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.adc(value); None},

            (Opcode::AND, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.and(value); None},
            (Opcode::AND, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.and(value); None},
            (Opcode::AND, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.and(value); None},
            (Opcode::AND, Operand::Imm(v)) => {self.and(v); None},
            (Opcode::AND, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.and(value); None},
            (Opcode::AND, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.and(value); None},
            (Opcode::AND, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.and(value); None},
            (Opcode::AND, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.and(value); None},

            (Opcode::ASL, Operand::Abs(a)) => {self.asl_abs(mem, a); None},
            (Opcode::ASL, Operand::AbsX(a)) => {self.asl_absx(mem, a); None},
            (Opcode::ASL, Operand::Impl) => {self.asl_acc(); None},
            (Opcode::ASL, Operand::Zpg(a)) => {self.asl_zpg(mem, a); None},
            (Opcode::ASL, Operand::ZpgX(a)) => {self.asl_zpgx(mem, a); None},

            (Opcode::BCC, Operand::Rel(o)) => {self.bcc(o); None},
            (Opcode::BCS, Operand::Rel(o)) => {self.bcs(o); None},
            (Opcode::BEQ, Operand::Rel(o)) => {self.beq(o); None},
            (Opcode::BIT, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.bit(value); None},
            (Opcode::BIT, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.bit(value); None},
            (Opcode::BMI, Operand::Rel(o)) => {self.bmi(o); None},
            (Opcode::BNE, Operand::Rel(o)) => {self.bne(o); None},
            (Opcode::BPL, Operand::Rel(o)) => {self.bpl(o); None},
            (Opcode::BRK, Operand::Impl) => {self.brk(mem); None}
            (Opcode::BVC, Operand::Rel(o)) => {self.bvc(o); None},
            (Opcode::BVS, Operand::Rel(o)) => {self.bvs(o); None},
            (Opcode::CLC, Operand::Impl) => {self.clc(); None},
            (Opcode::CLD, Operand::Impl) => {self.cld(); None},
            (Opcode::CLI, Operand::Impl) => {self.cli(); None},
            (Opcode::CLV, Operand::Impl) => {self.clv(); None},

            (Opcode::CMP, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::Imm(v)) => {self.cmp(v); None},
            (Opcode::CMP, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.cmp(value); None},
            (Opcode::CMP, Operand::ZpgY(a)) => {let value = self.read_zpgy(mem, a); self.cmp(value); None},

            (Opcode::CPX, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.cpx(value); None},
            (Opcode::CPX, Operand::Imm(v)) => {self.cpx(v); None},
            (Opcode::CPX, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.cpx(value); None},

            (Opcode::CPY, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.cpy(value); None},
            (Opcode::CPY, Operand::Imm(v)) => {self.cpy(v); None},
            (Opcode::CPY, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.cpy(value); None},

            (Opcode::DEC, Operand::Abs(a)) => {self.dec_abs(mem, a); None},
            (Opcode::DEC, Operand::AbsX(a)) => {self.dec_absx(mem, a); None},
            (Opcode::DEC, Operand::Zpg(a)) => {self.dec_zpg(mem, a); None},
            (Opcode::DEC, Operand::ZpgX(a)) => {self.dec_zpgx(mem, a); None},

            (Opcode::DEX, Operand::Impl) => {self.dex(); None},
            (Opcode::DEY, Operand::Impl) => {self.dey(); None},

            (Opcode::EOR, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::Imm(v)) => {self.eor(v); None},
            (Opcode::EOR, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.eor(value); None},
            (Opcode::EOR, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.eor(value); None},

            (Opcode::INC, Operand::Abs(a)) => {self.inc_abs(mem, a); None},
            (Opcode::INC, Operand::AbsX(a)) => {self.inc_absx(mem, a); None},
            (Opcode::INC, Operand::Zpg(a)) => {self.inc_zpg(mem, a); None},
            (Opcode::INC, Operand::ZpgX(a)) => {self.inc_zpgx(mem, a); None},

            (Opcode::INX, Operand::Impl) => {self.inx(); None},
            (Opcode::INY, Operand::Impl) => {self.iny(); None},

            (Opcode::JMP, Operand::Abs(a)) => {self.jmp(a); None},
            (Opcode::JMP, Operand::Ind(a)) => {let address = self.read_word(mem, a); self.jmp(address); None},

            (Opcode::JSR, Operand::Abs(a)) => {self.jsr(mem, a); None},

            (Opcode::LDA, Operand::Abs(a)) => {let address = self.read_byte(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::AbsX(a)) => {let address = self.read_absx(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::AbsY(a)) => {let address = self.read_absy(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::Imm(v)) => {self.lda(v); None},
            (Opcode::LDA, Operand::XInd(a)) => {let address = self.read_xind(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::IndY(a)) => {let address = self.read_indy(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::Zpg(a)) => {let address = self.read_zpg(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::ZpgX(a)) => {let address = self.read_zpgx(mem, a); self.lda(address); None},
            (Opcode::LDA, Operand::ZpgY(a)) => {let address = self.read_zpgy(mem, a); self.lda(address); None},

            (Opcode::LDX, Operand::Abs(a)) => {let address = self.read_byte(mem, a); self.ldx(address); None},
            (Opcode::LDX, Operand::AbsY(a)) => {let address = self.read_absy(mem, a); self.ldx(address); None},
            (Opcode::LDX, Operand::Imm(v)) => {self.ldx(v); None},
            (Opcode::LDX, Operand::Zpg(a)) => {let address = self.read_zpg(mem, a); self.ldx(address); None},
            (Opcode::LDX, Operand::ZpgY(a)) => {let address = self.read_zpgy(mem, a); self.ldx(address); None},

            (Opcode::LDY, Operand::Abs(a)) => {let address = self.read_byte(mem, a); self.ldy(address); None},
            (Opcode::LDY, Operand::AbsX(a)) => {let address = self.read_absx(mem, a); self.ldy(address); None},
            (Opcode::LDY, Operand::Imm(v)) => {self.ldy(v); None},
            (Opcode::LDY, Operand::Zpg(a)) => {let address = self.read_zpg(mem, a); self.ldy(address); None},
            (Opcode::LDY, Operand::ZpgX(a)) => {let address = self.read_zpgx(mem, a); self.ldy(address); None},

            (Opcode::LSR, Operand::Abs(a)) => {self.lsr_abs(mem, a); None},
            (Opcode::LSR, Operand::AbsX(a)) => {self.lsr_absx(mem, a); None},
            (Opcode::LSR, Operand::Impl) => {self.lsr_acc(); None},
            (Opcode::LSR, Operand::Zpg(a)) => {self.lsr_zpg(mem, a); None},
            (Opcode::LSR, Operand::ZpgX(a)) => {self.lsr_zpgx(mem, a); None},

            (Opcode::NOP, Operand::Impl) => {self.nop(); None},

            (Opcode::ORA, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::Imm(v)) => {self.ora(v); None},
            (Opcode::ORA, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.ora(value); None},
            (Opcode::ORA, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.ora(value); None},

            (Opcode::PHA, Operand::Impl) => {self.pha(mem); None},
            (Opcode::PHP, Operand::Impl) => {self.php(mem); None},
            (Opcode::PLA, Operand::Impl) => {self.pla(mem); None},
            (Opcode::PLP, Operand::Impl) => {self.plp(mem); None},

            (Opcode::ROL, Operand::Abs(a)) => {self.rol_abs(mem, a); None},
            (Opcode::ROL, Operand::AbsX(a)) => {self.rol_absx(mem, a); None},
            (Opcode::ROL, Operand::Impl) => {self.rol_acc(); None},
            (Opcode::ROL, Operand::Zpg(a)) => {self.rol_zpg(mem, a); None},
            (Opcode::ROL, Operand::ZpgX(a)) => {self.rol_zpgx(mem, a); None},

            (Opcode::ROR, Operand::Abs(a)) => {self.ror_abs(mem, a); None},
            (Opcode::ROR, Operand::AbsX(a)) => {self.ror_absx(mem, a); None},
            (Opcode::ROR, Operand::Impl) => {self.ror_acc(); None},
            (Opcode::ROR, Operand::Zpg(a)) => {self.ror_zpg(mem, a); None},
            (Opcode::ROR, Operand::ZpgX(a)) => {self.ror_zpgx(mem, a); None},

            (Opcode::RTS, Operand::Impl) => {self.rts(mem); None},
            (Opcode::RTI, Operand::Impl) => {self.rti(mem); None},

            (Opcode::SBC, Operand::Abs(a)) => {let value = self.read_byte(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::AbsX(a)) => {let value = self.read_absx(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::AbsY(a)) => {let value = self.read_absy(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::Imm(v)) => {self.sbc(v); None},
            (Opcode::SBC, Operand::XInd(a)) => {let value = self.read_xind(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::IndY(a)) => {let value = self.read_indy(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::Zpg(a)) => {let value = self.read_zpg(mem, a); self.sbc(value); None},
            (Opcode::SBC, Operand::ZpgX(a)) => {let value = self.read_zpgx(mem, a); self.sbc(value); None},


            (Opcode::SEC, Operand::Impl) => {self.sec(); None},
            (Opcode::SED, Operand::Impl) => {self.sed(); None},
            (Opcode::SEI, Operand::Impl) => {self.sei(); None},

            (Opcode::STA, Operand::Abs(a)) => {self.sta_abs(mem, a); None},
            (Opcode::STA, Operand::AbsX(a)) => {self.sta_absx(mem, a); None},
            (Opcode::STA, Operand::AbsY(a)) => {self.sta_absy(mem, a); None},
            (Opcode::STA, Operand::XInd(a)) => {self.sta_xind(mem, a); None},
            (Opcode::STA, Operand::IndY(a)) => {self.sta_indy(mem, a); None},
            (Opcode::STA, Operand::Zpg(a)) => {self.sta_zpg(mem, a); None},
            (Opcode::STA, Operand::ZpgX(a)) => {self.sta_zpgx(mem, a); None},

            (Opcode::STX, Operand::Abs(a)) => {self.stx_abs(mem, a); None},
            (Opcode::STX, Operand::Zpg(a)) => {self.stx_zpg(mem, a); None},
            (Opcode::STX, Operand::ZpgY(a)) => {self.stx_zpgy(mem, a); None},

            (Opcode::STY, Operand::Abs(a)) => {self.sty_abs(mem, a); None},
            (Opcode::STY, Operand::Zpg(a)) => {self.sty_zpg(mem, a); None},
            (Opcode::STY, Operand::ZpgX(a)) => {self.sty_zpgx(mem, a); None},

            (Opcode::TAX, Operand::Impl) => {self.tax(); None},
            (Opcode::TSX, Operand::Impl) => {self.tsx(); None},
            (Opcode::TXA, Operand::Impl) => {self.txa(); None},
            (Opcode::TXS, Operand::Impl) => {self.txs(); None},
            (Opcode::TAY, Operand::Impl) => {self.tay(); None},
            (Opcode::TYA, Operand::Impl) => {self.tya(); None},
            (Opcode::Illegal, _) => Some(CpuError::IllegalInstruction),
            (_, _) => Some(CpuError::UnimplementedInstruction)
        };

        return result
    }

    pub fn handle_error(&mut self, error: CpuError) {
        match error {
            CpuError::IllegalInstruction => println!("\nIllegal Instruction encountered\n"),
            CpuError::UnimplementedInstruction => println!("\nUnimplemented Instruction encountered\n"),
            CpuError::IncompatibleAddrMode => println!("\nAddress Mode was incompatible with the supplied instruction\n"),
            CpuError::TrapDetected(inst) => println!("\nCPU entered trap: {}\n", inst),
        };

        for (pc, instruction) in self.previous_instructions.iter() {
            println!("{:04X}: {:?}; {}", pc, instruction, instruction);
        }
    }

    pub fn step(&mut self, mem: &mut Memory) -> Option<CpuError> {
        return if cfg!(debug_assertions) {
            let current_cycles = self.cycles;
            let instruction = match self.fetch_instruction(mem) {
                Ok(inst) => inst,
                Err(e) => return Some(e)
            };
            let result = self.execute_instruction(mem, instruction);
            let cycles_taken = self.cycles - current_cycles;
            println!("{} cycles: {}\t\t{}\n", cycles_taken, instruction, self);
            result
        } else {
            let instruction = match self.fetch_instruction(mem) {
                Ok(inst) => inst,
                Err(e) => match e {
                    CpuError::IllegalInstruction => return Some(e),
                    CpuError::UnimplementedInstruction => return Some(e),
                    CpuError::IncompatibleAddrMode => return Some(e),
                    CpuError::TrapDetected(inst) => inst
                }
            };
            self.execute_instruction(mem, instruction)
        }
    }

    pub fn run(&mut self, mem: &mut Memory) {
        const CYCLE_COUNT: usize = 1_000_000;
        const CPU_FREQ: usize = 1_000_000_000;
        const BLOCK_TIME: f64 = CYCLE_COUNT as f64 / CPU_FREQ as f64;

        let mut halt = false;
        let mut pre_cycle = 0;
        let mut pre_time = std::time::Instant::now();
        let mut cycle_counter = 0;

        while !halt {
            let result = self.step(mem);
            if let Some(e) = result {
                halt = true;
                self.handle_error(e);
            }
            cycle_counter += self.cycles - pre_cycle;
            pre_cycle = self.cycles;
            if cycle_counter > CYCLE_COUNT {
                let block_time = pre_time.elapsed().as_secs_f64();
                let block_time_left = BLOCK_TIME - block_time;
                if block_time_left > 0.0 {std::thread::sleep(std::time::Duration::from_secs_f64(block_time_left));}

                let total_time = pre_time.elapsed().as_secs_f64();
                let time_per_cycle = total_time / cycle_counter as f64;
                let hertz = 1.0 / time_per_cycle;
                let mega_hertz = hertz * 1e-6;
                println!("{} MHz", mega_hertz);
                pre_time = std::time::Instant::now();
                cycle_counter = 0;
            }
        }
    }

    fn push_byte(&mut self, mem: &mut Memory, byte: u8) {
        self.write_byte(mem, 0x0100 + self.sp as u16, byte);
        self.sp = self.sp.wrapping_sub(1);
        self.cycles += 1;
    }

    fn push_word(&mut self, mem: &mut Memory, word: u16) {
        let [word_lo, word_hi] = word.to_le_bytes();
        self.push_byte(mem, word_hi);
        self.push_byte(mem, word_lo);
    }

    fn pull_byte(&mut self, mem: &Memory) -> u8 {
        self.sp = self.sp.wrapping_add(1);
        self.cycles += 1;
        self.read_byte(mem, 0x0100 + self.sp as u16)
    }

    fn pull_word(&mut self, mem: &Memory) -> u16 {
        let word_lo = self.pull_byte(mem);
        let word_hi = self.pull_byte(mem);
        return u16::from_le_bytes([word_lo, word_hi])
    }

    fn read_absx(&mut self, mem: &Memory, address: u16) -> u8 {
        let new_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (new_address & 0xFF00) {
            self.cycles += 1;
        }
        return self.read_byte(mem, new_address)
    }

    fn read_absy(&mut self, mem: &Memory, address: u16) -> u8 {
        let new_address = address.wrapping_add(self.y as u16);
        if (address & 0xFF00) != (new_address & 0xFF00) {
            self.cycles += 1;
        }
        return self.read_byte(mem, new_address)
    }

    fn read_ind(&mut self, mem: &Memory, address: u16) -> u8 {
        let ind_address = self.read_word(mem, address);
        return self.read_byte(mem, ind_address)
    }

    fn read_xind(&mut self, mem: &Memory, address: u8) -> u8 {
        let ind_address = self.read_word(mem, address.wrapping_add(self.x) as u16);
        return self.read_byte(mem, ind_address)
    }

    fn read_indy(&mut self, mem: &Memory, address: u8) -> u8 {
        let ind_address = self.read_word(mem, address as u16);
        let final_address = ind_address.wrapping_add(self.y as u16);
        if (ind_address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        return self.read_byte(mem, final_address)
    }

    fn read_zpg(&mut self, mem: &Memory, zeropage_address: u8) -> u8 {
        return self.read_byte(mem, zeropage_address as u16)
    }

    fn read_zpgx(&mut self, mem: &Memory, zeropage_address: u8) -> u8 {
        return self.read_byte(mem, zeropage_address.wrapping_add(self.x) as u16)
    }

    fn read_zpgy(&mut self, mem: &Memory, zeropage_address: u8) -> u8 {
        return self.read_byte(mem, zeropage_address.wrapping_add(self.y) as u16)
    }

    fn adc(&mut self, byte: u8) {
        fn carrying_add(lhs: u8, rhs: u8, carry: bool) -> (u8, bool) {
            let (a, b) = lhs.overflowing_add(rhs);
            let (c, d) = a.overflowing_add(carry as u8);
            return (c, b || d)
        }

        if self.sr.get(FLAG_D) {
            let a = self.ac as u32;
            let v = byte as u32;

            let mut lo = (a & 0x0F) + (v & 0x0F) + self.sr.get(FLAG_C) as u32;
            let mut hi = (a & 0xF0) + (v & 0xF0);

            self.sr.set(FLAG_Z, ((lo + hi) & 0xFF) == 0);
            if lo > 0x09 {hi += 0x10; lo += 0x06;}
            self.sr.set(FLAG_N,(hi & 0x80) != 0);
            let overflow = (a^v)&(a^hi)&0x80 != 0;
            self.sr.set(FLAG_V, overflow);
            if hi > 0x90 {hi += 0x60;}
            self.sr.set(FLAG_C, (hi >> 8) != 0);

            self.ac = ((lo & 0x0F) | (hi & 0xF0)) as u8;

        } else {
            let (result, carry) = carrying_add(self.ac, byte, self.sr.get(FLAG_C));
            let overflow = (self.ac^result)&(byte^result)&0x80 != 0;
            self.sr.set(FLAG_N, (result & FLAG_N) != 0);
            self.sr.set(FLAG_Z, result == 0);
            self.sr.set(FLAG_C, carry);
            self.sr.set(FLAG_V, overflow);
            self.ac = result;
        }
    }

    fn sbc(&mut self, byte: u8) {
        fn carrying_add(lhs: u8, rhs: u8, carry: bool) -> (u8, bool) {
            let (a, b) = lhs.overflowing_add(rhs);
            let (c, d) = a.overflowing_add(carry as u8);
            return (c, b || d)
        }

        if self.sr.get(FLAG_D) {
            //println!("BCD sub");
            let a = self.ac as u32;
            let v = byte as u32;
            let carry = !self.sr.get(FLAG_C) as u32;
            let t = a.wrapping_sub(v).wrapping_sub(carry);

            let mut lo = (a & 0x0F).wrapping_sub(v & 0x0F).wrapping_sub(carry);
            let mut hi = (a & 0xF0).wrapping_sub(v & 0xF0);

            if (lo & 0x10) != 0 {lo -= 0x06; hi -= 1;}
            let overflow = (a^v)&(a^t)&0x80 != 0;
            self.sr.set(FLAG_V, overflow);
            self.sr.set(FLAG_C, (t >> 8) == 0);
            self.sr.set(FLAG_Z, (t << 8) == 0);
            self.sr.set(FLAG_N, (t & 0x80) != 0);
            if (hi & 0x0100) != 0 {hi -= 0x60};

            let result = ((lo & 0x0F) | (hi & 0xF0)) as u8;
            //println!("{:02X} - {:02X} - {} = {:02X}", self.ac, byte, carry, result);
            self.ac = result;

        } else {
            let (result, carry) = carrying_add(self.ac, !byte, self.sr.get(FLAG_C));
            let overflow = (self.ac^result)&(!byte^result)&0x80 != 0;
            self.sr.set(FLAG_N, (result & FLAG_N) != 0);
            self.sr.set(FLAG_Z, result == 0);
            self.sr.set(FLAG_C, carry);
            self.sr.set(FLAG_V, overflow);
            self.ac = result;
        }
    }

    fn and(&mut self, byte: u8) {
        self.ac &= byte;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn asl(&mut self, byte: u8) -> u8 {
        let (value, carry) = byte.overflowing_mul(2);
        self.sr.set(FLAG_N, (FLAG_N & value) != 0);
        self.sr.set(FLAG_Z, value == 0);
        self.sr.set(FLAG_C, carry);
        return value
    }

    fn asl_acc(&mut self) {
        self.ac = self.asl(self.ac);
        self.cycles += 1;
    }

    fn asl_abs(&mut self, mem: &mut Memory, address: u16) {
        let pre_value = self.read_byte(mem, address);
        let value = self.asl(pre_value);
        self.write_byte(mem, address, value);
    }

    fn asl_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let pre_value = self.read_byte(mem, final_address);
        let value = self.asl(pre_value);
        self.write_byte(mem, final_address, value);
    }

    fn asl_zpg(&mut self, mem: &mut Memory, address: u8) {
        let pre_value = self.read_byte(mem, address as u16);
        let value = self.asl(pre_value);
        self.write_byte(mem, address as u16, value);
    }

    fn asl_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let final_address = address.wrapping_add(self.x);
        let pre_value = self.read_byte(mem, final_address as u16);
        let value = self.asl(pre_value);
        self.write_byte(mem, final_address as u16, value);
    }

    fn bcc(&mut self, offset: i8) {
        if !self.sr.get(FLAG_C) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn bcs(&mut self, offset: i8) {
        if self.sr.get(FLAG_C) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn beq(&mut self, offset: i8) {
        if self.sr.get(FLAG_Z) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn bit(&mut self, byte: u8) {
        self.sr.set(FLAG_Z, (self.ac & byte) == 0);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_V, (FLAG_V & byte) != 0);
    }

    fn bmi(&mut self, offset: i8) {
        if self.sr.get(FLAG_N) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn bne(&mut self, offset: i8) {
        if !self.sr.get(FLAG_Z) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn bpl(&mut self, offset: i8) {
        if !self.sr.get(FLAG_N) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn brk(&mut self, mem: &mut Memory) {
        self.push_word(mem, self.pc.wrapping_add(1));
        self.push_byte(mem, self.sr.0 | 0b0011_0000);
        self.pc = self.read_word(mem, 0xFFFE);
        self.sr.set(FLAG_I, true);
        self.cycles -= 2;
    }

    fn bvc(&mut self, offset: i8) {
        if !self.sr.get(FLAG_V) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn bvs(&mut self, offset: i8) {
        if self.sr.get(FLAG_V) {
            let new_pc = self.pc.wrapping_add_signed(offset as i16);
            self.cycles += if (new_pc & 0xFF00) == (self.pc & 0xFF00) {1} else {2};
            self.pc = new_pc;
        }
    }

    fn clc(&mut self) {
        self.sr.set(FLAG_C, false);
        self.cycles += 1;
    }

    fn cld(&mut self) {
        self.sr.set(FLAG_D, false);
        self.cycles += 1;
    }

    fn cli(&mut self) {
        self.sr.set(FLAG_I, false);
        self.cycles += 1;
    }

    fn clv(&mut self) {
        self.sr.set(FLAG_V, false);
        self.cycles += 1;
    }

    fn cmp(&mut self, byte: u8) {
        //if self.sr.get(FLAG_D) {println!("AC: {:02X} Byte: {:02X}", self.ac, byte);}
        let result = self.ac.wrapping_sub(byte);
        self.sr.set(FLAG_N, (result & FLAG_N) != 0);
        self.sr.set(FLAG_Z, result == 0);
        self.sr.set(FLAG_C, byte <= self.ac);
    }

    fn cpx(&mut self, byte: u8) {
        let result = self.x.wrapping_sub(byte);
        self.sr.set(FLAG_N, (result & FLAG_N) != 0);
        self.sr.set(FLAG_Z, result == 0);
        self.sr.set(FLAG_C, byte <= self.x);
    }

    fn cpy(&mut self, byte: u8) {
        let result = self.y.wrapping_sub(byte);
        self.sr.set(FLAG_N, (result & FLAG_N) != 0);
        self.sr.set(FLAG_Z, result == 0);
        self.sr.set(FLAG_C, byte <= self.y);
    }

    fn dec_abs(&mut self, mem: &mut Memory, address: u16) {
        let byte = self.read_byte(mem, address).wrapping_sub(1);
        self.write_byte(mem, address, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn dec_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let byte = self.read_byte(mem, final_address).wrapping_sub(1);
        self.write_byte(mem, final_address, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn dec_zpg(&mut self, mem: &mut Memory, address: u8) {
        let byte = self.read_byte(mem, address as u16).wrapping_sub(1);
        self.write_byte(mem, address as u16, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn dec_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let byte = self.read_byte(mem, address.wrapping_add(self.x) as u16).wrapping_sub(1);
        self.write_byte(mem, address.wrapping_add(self.x) as u16, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn dex(&mut self) {
        self.x = self.x.wrapping_sub(1);
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.x & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.x == 0);
    }

    fn dey(&mut self) {
        self.y = self.y.wrapping_sub(1);
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.y & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.y == 0);
    }

    fn eor(&mut self, byte: u8) {
        self.ac ^= byte;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn inc_abs(&mut self, mem: &mut Memory, address: u16) {
        let byte = self.read_byte(mem, address).wrapping_add(1);
        self.write_byte(mem, address, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn inc_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let byte = self.read_byte(mem, final_address).wrapping_add(1);
        self.write_byte(mem, final_address, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn inc_zpg(&mut self, mem: &mut Memory, address: u8) {
        let byte = self.read_byte(mem, address as u16).wrapping_add(1);
        self.write_byte(mem, address as u16, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn inc_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let byte = self.read_byte(mem, address.wrapping_add(self.x) as u16).wrapping_add(1);
        self.write_byte(mem, address.wrapping_add(self.x) as u16, byte);
        self.sr.set(FLAG_N, (FLAG_N & byte) != 0);
        self.sr.set(FLAG_Z, byte == 0);
    }

    fn inx(&mut self) {
        self.x = self.x.wrapping_add(1);
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.x & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.x == 0);
    }

    fn iny(&mut self) {
        self.y = self.y.wrapping_add(1);
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.y & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.y == 0);
    }

    fn jmp(&mut self, address: u16) {
        self.pc = address;
    }

    fn jsr(&mut self, mem: &mut Memory, address: u16) {
        self.push_word(mem, self.pc.wrapping_sub(1));
        self.pc = address;
        self.cycles -= 1;
    }

    fn lda(&mut self, byte: u8) {
        self.ac = byte;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn ldx(&mut self, byte: u8) {
        self.x = byte;
        self.sr.set(FLAG_N, (self.x & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.x == 0);
    }

    fn ldy(&mut self, byte: u8) {
        self.y = byte;
        self.sr.set(FLAG_N, (self.y & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.y == 0);
    }

    fn lsr(&mut self, byte: u8) -> u8 {
        let value = byte / 2;
        let carry = (byte % 2) != 0;
        self.sr.set(FLAG_N, false);
        self.sr.set(FLAG_Z, value == 0);
        self.sr.set(FLAG_C, carry);
        return value
    }

    fn lsr_acc(&mut self) {
        self.ac = self.lsr(self.ac);
        self.cycles += 1;
    }

    fn lsr_abs(&mut self, mem: &mut Memory, address: u16) {
        let pre_value = self.read_byte(mem, address);
        let value = self.lsr(pre_value);
        self.write_byte(mem, address, value);
    }

    fn lsr_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let pre_value = self.read_byte(mem, final_address);
        let value = self.lsr(pre_value);
        self.write_byte(mem, final_address, value);
    }

    fn lsr_zpg(&mut self, mem: &mut Memory, address: u8) {
        let pre_value = self.read_byte(mem, address as u16);
        let value = self.lsr(pre_value);
        self.write_byte(mem, address as u16, value);
    }

    fn lsr_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let final_address = address.wrapping_add(self.x);
        let pre_value = self.read_byte(mem, final_address as u16);
        let value = self.lsr(pre_value);
        self.write_byte(mem, final_address as u16, value);
    }

    fn nop(&mut self) {
        self.cycles += 1;
    }

    fn ora(&mut self, byte: u8) {
        self.ac |= byte;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn pha(&mut self, mem: &mut Memory) {
        self.push_byte(mem, self.ac);
    }

    fn pla(&mut self, mem: &Memory) {
        self.ac = self.pull_byte(mem);
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn php(&mut self, mem: &mut Memory) {
        self.push_byte(mem, self.sr.0 | 0b0011_0000);
    }

    fn plp(&mut self, mem: &Memory) {
        self.sr = StatusRegister(self.pull_byte(mem) & 0b1100_1111);
        self.cycles += 1;
    }

    fn rol(&mut self, byte: u8) -> u8 {
        let low_bit = if self.sr.get(FLAG_C) {1} else {0};
        let (pre_value, carry) = byte.overflowing_mul(2);
        let value = pre_value | low_bit;
        self.sr.set(FLAG_N, (FLAG_N & value) != 0);
        self.sr.set(FLAG_Z, value == 0);
        self.sr.set(FLAG_C, carry);
        return value
    }

    fn rol_acc(&mut self) {
        self.ac = self.rol(self.ac);
        self.cycles += 1;
    }

    fn rol_abs(&mut self, mem: &mut Memory, address: u16) {
        let pre_value = self.read_byte(mem, address);
        let value = self.rol(pre_value);
        self.write_byte(mem, address, value);
    }

    fn rol_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let pre_value = self.read_byte(mem, final_address);
        let value = self.rol(pre_value);
        self.write_byte(mem, final_address, value);
    }

    fn rol_zpg(&mut self, mem: &mut Memory, address: u8) {
        let pre_value = self.read_byte(mem, address as u16);
        let value = self.rol(pre_value);
        self.write_byte(mem, address as u16, value);
    }

    fn rol_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let final_address = address.wrapping_add(self.x);
        let pre_value = self.read_byte(mem, final_address as u16);
        let value = self.rol(pre_value);
        self.write_byte(mem, final_address as u16, value);
    }

    fn ror(&mut self, byte: u8) -> u8 {
        let high_bit = if self.sr.get(FLAG_C) {FLAG_N} else {0};
        let value = (byte / 2) | high_bit;
        let carry = (byte % 2) != 0;
        self.sr.set(FLAG_N, self.sr.get(FLAG_C));
        self.sr.set(FLAG_Z, value == 0);
        self.sr.set(FLAG_C, carry);
        return value
    }

    fn ror_acc(&mut self) {
        self.ac = self.ror(self.ac);
        self.cycles += 1;
    }

    fn ror_abs(&mut self, mem: &mut Memory, address: u16) {
        let pre_value = self.read_byte(mem, address);
        let value = self.ror(pre_value);
        self.write_byte(mem, address, value);
    }

    fn ror_absx(&mut self, mem: &mut Memory, address: u16) {
        let final_address = address.wrapping_add(self.x as u16);
        if (address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        let pre_value = self.read_byte(mem, final_address);
        let value = self.ror(pre_value);
        self.write_byte(mem, final_address, value);
    }

    fn ror_zpg(&mut self, mem: &mut Memory, address: u8) {
        let pre_value = self.read_byte(mem, address as u16);
        let value = self.ror(pre_value);
        self.write_byte(mem, address as u16, value);
    }

    fn ror_zpgx(&mut self, mem: &mut Memory, address: u8) {
        let final_address = address.wrapping_add(self.x);
        let pre_value = self.read_byte(mem, final_address as u16);
        let value = self.ror(pre_value);
        self.write_byte(mem, final_address as u16, value);
    }

    fn rts(&mut self, mem: &Memory) {
        self.pc = self.pull_word(mem).wrapping_add(1);
        self.cycles += 1;
    }

    fn rti(&mut self, mem: &Memory) {
        self.sr = StatusRegister(self.pull_byte(mem) & 0b1100_1111);
        self.pc = self.pull_word(mem);
        self.cycles += 1;
    }

    fn sec(&mut self) {
        self.sr.set(FLAG_C, true);
        self.cycles += 1;
    }

    fn sed(&mut self) {
        self.sr.set(FLAG_D, true);
        self.cycles += 1;
    }

    fn sei(&mut self) {
        self.sr.set(FLAG_I, true);
        self.cycles += 1;
    }

    fn sta_abs(&mut self, mem: &mut Memory, absolute_address: u16) {
        self.write_byte(mem, absolute_address, self.ac);
    }

    fn sta_absx(&mut self, mem: &mut Memory, absolute_address: u16) {
        let new_address = absolute_address.wrapping_add(self.x as u16);
        if (absolute_address & 0xFF00) != (new_address & 0xFF00) {
            self.cycles += 1;
        }
        self.write_byte(mem, new_address, self.ac);
    }

    fn sta_absy(&mut self, mem: &mut Memory, absolute_address: u16) {
        let new_address = absolute_address.wrapping_add(self.y as u16);
        if (absolute_address & 0xFF00) != (new_address & 0xFF00) {
            self.cycles += 1;
        }
        self.write_byte(mem, new_address, self.ac);
    }

    fn sta_xind(&mut self, mem: &mut Memory, address: u8) {
        let ind_address = self.read_word(mem, address.wrapping_add(self.x) as u16);
        self.write_byte(mem, ind_address, self.ac);
    }

    fn sta_indy(&mut self, mem: &mut Memory, address: u8) {
        let ind_address = self.read_word(mem, address as u16);
        let final_address = ind_address.wrapping_add(self.y as u16);
        if (ind_address & 0xFF00) != (final_address & 0xFF00) {
            self.cycles += 1;
        }
        self.write_byte(mem, final_address, self.ac);
    }

    fn sta_zpg(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address as u16, self.ac);
    }

    fn sta_zpgx(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address.wrapping_add(self.x) as u16, self.ac);
    }

    fn stx_abs(&mut self, mem: &mut Memory, absolute_address: u16) {
        self.write_byte(mem, absolute_address, self.x);
    }

    fn stx_zpg(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address as u16, self.x);
    }

    fn stx_zpgy(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address.wrapping_add(self.y) as u16, self.x);
    }

    fn sty_abs(&mut self, mem: &mut Memory, absolute_address: u16) {
        self.write_byte(mem, absolute_address, self.y);
    }

    fn sty_zpg(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address as u16, self.y);
    }

    fn sty_zpgx(&mut self, mem: &mut Memory, zeropage_address: u8) {
        self.write_byte(mem, zeropage_address.wrapping_add(self.x) as u16, self.y);
    }

    fn tax(&mut self) {
        self.x = self.ac;
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.x & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.x == 0);
    }

    fn tay(&mut self) {
        self.y = self.ac;
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.y & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.y == 0);
    }

    fn tsx(&mut self) {
        self.x = self.sp;
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.x & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.x == 0);
    }

    fn txa(&mut self) {
        self.ac = self.x;
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }

    fn txs(&mut self) {
        self.sp = self.x;
        self.cycles += 1;
    }

    fn tya(&mut self) {
        self.ac = self.y;
        self.cycles += 1;
        self.sr.set(FLAG_N, (self.ac & FLAG_N) != 0);
        self.sr.set(FLAG_Z, self.ac == 0);
    }
}


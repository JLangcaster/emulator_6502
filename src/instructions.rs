use std::fmt::{Debug, Display, Formatter, Write};
use AddrMode::*;
use Opcode::*;
use crate::cpu::{Cpu, Memory};

#[derive(Copy, Clone, strum::Display, Debug)]
pub enum AddrMode {
    Abs,
    AbsX,
    AbsY,
    Imm,
    Impl,
    Ind,
    XInd,
    IndY,
    Rel,
    Zpg,
    ZpgX,
    ZpgY
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Operand {
    Abs(u16),
    AbsX(u16),
    AbsY(u16),
    Imm(u8),
    Impl,
    Ind(u16),
    XInd(u8),
    IndY(u8),
    Rel(i8),
    Zpg(u8),
    ZpgX(u8),
    ZpgY(u8),
}

impl Operand {
    fn to_addr_mode(&self) -> AddrMode {
        return match self {
            Operand::Abs(_) => Abs,
            Operand::AbsX(_) => AbsX,
            Operand::AbsY(_) => AbsY,
            Operand::Imm(_) => Imm,
            Operand::Impl => Impl,
            Operand::Ind(_) => Ind,
            Operand::XInd(_) => XInd,
            Operand::IndY(_) => IndY,
            Operand::Rel(_) => Rel,
            Operand::Zpg(_) => Zpg,
            Operand::ZpgX(_) => ZpgX,
            Operand::ZpgY(_) => ZpgY
        }
    }
}

impl Debug for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Operand::*;
        return match self {
            Abs(v) => f.write_fmt(format_args!("{:02X} {:02X}", v.to_le_bytes()[0], v.to_le_bytes()[1])),
            AbsX(v) => f.write_fmt(format_args!("{:02X} {:02X}", v.to_le_bytes()[0], v.to_le_bytes()[1])),
            AbsY(v) => f.write_fmt(format_args!("{:02X} {:02X}", v.to_le_bytes()[0], v.to_le_bytes()[1])),
            Imm(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            Impl => f.write_str("     "),
            Ind(v) => f.write_fmt(format_args!("{:02X} {:02X}", v.to_le_bytes()[0], v.to_le_bytes()[1])),
            XInd(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            IndY(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            Rel(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            Zpg(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            ZpgX(v) => f.write_fmt(format_args!("{:02X}   ", v)),
            ZpgY(v) => f.write_fmt(format_args!("{:02X}   ", v)),
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Operand::*;
        return match self {
            Abs(v) => f.write_fmt(format_args!("${:04X}", v)),
            AbsX(v) => f.write_fmt(format_args!("${:04X},X", v)),
            AbsY(v) => f.write_fmt(format_args!("${:04X},Y", v)),
            Imm(v) => f.write_fmt(format_args!("#${:02X}", v)),
            Impl => f.write_str(""),
            Ind(v) => f.write_fmt(format_args!("(${:04X})", v)),
            XInd(v) => f.write_fmt(format_args!("(${:02X},X)", v)),
            IndY(v) => f.write_fmt(format_args!("(${:02X}),Y", v)),
            Rel(v) => if v >= &0 {
                f.write_fmt(format_args!("PC + ${:02X}", v))
            } else {
                f.write_fmt(format_args!("PC - ${:02X}", v.unsigned_abs()))
            },
            Zpg(v) => f.write_fmt(format_args!("${:02X}", v)),
            ZpgX(v) => f.write_fmt(format_args!("${:02X},X", v)),
            ZpgY(v) => f.write_fmt(format_args!("${:02X},Y", v)),
        }
    }
}

#[derive(strum::Display, Copy, Clone, Eq, PartialEq, Debug)]
pub enum Opcode {
    Illegal,
    ADC,
    AND,
    ASL,
    BCC,
    BCS,
    BEQ,
    BIT,
    BMI,
    BNE,
    BPL,
    BRK,
    BVC,
    BVS,
    CLC,
    CLD,
    CLI,
    CLV,
    CMP,
    CPX,
    CPY,
    DEC,
    DEX,
    DEY,
    EOR,
    INC,
    INX,
    INY,
    JMP,
    JSR,
    LDA,
    LDX,
    LDY,
    LSR,
    NOP,
    ORA,
    PHA,
    PHP,
    PLA,
    PLP,
    ROL,
    ROR,
    RTI,
    RTS,
    SBC,
    SEC,
    SED,
    SEI,
    STA,
    STX,
    STY,
    TAX,
    TAY,
    TSX,
    TXA,
    TXS,
    TYA
}

pub const INST_TABLE: [(Opcode, AddrMode); 256] = [
//  0               1               2               3               4               5               6               7               8               9               A               B               C               D               E               F
    (BRK, Impl),    (ORA, XInd),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ORA, Zpg),     (ASL, Zpg),     (Illegal, Impl),(PHP, Impl),    (ORA, Imm),     (ASL, Impl),    (Illegal, Impl),(Illegal, Impl),(ORA, Abs),     (ASL, Abs),     (Illegal, Impl),
    (BPL, Rel),     (ORA, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ORA, ZpgX),    (ASL, ZpgX),    (Illegal, Impl),(CLC, Impl),    (ORA, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ORA, AbsX),    (ASL, AbsX),    (Illegal, Impl),
    (JSR, Abs),     (AND, XInd),    (Illegal, Impl),(Illegal, Impl),(BIT, Zpg),     (AND, Zpg),     (ROL, Zpg),     (Illegal, Impl),(PLP, Impl),    (AND, Imm),     (ROL, Impl),    (Illegal, Impl),(BIT, Abs),     (AND, Abs),     (ROL, Abs),     (Illegal, Impl),
    (BMI, Rel),     (AND, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(AND, ZpgX),    (ROL, ZpgX),    (Illegal, Impl),(SEC, Impl),    (AND, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(AND, AbsX),    (ROL, AbsX),    (Illegal, Impl),
    (RTI, Impl),    (EOR, XInd),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(EOR, Zpg),     (LSR, Zpg),     (Illegal, Impl),(PHA, Impl),    (EOR, Imm),     (LSR, Impl),    (Illegal, Impl),(JMP, Abs),     (EOR, Abs),     (LSR, Abs),     (Illegal, Impl),
    (BVC, Rel),     (EOR, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(EOR, ZpgX),    (LSR, ZpgX),    (Illegal, Impl),(CLI, Impl),    (EOR, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(EOR, AbsX),    (LSR, AbsX),    (Illegal, Impl),
    (RTS, Impl),    (ADC, XInd),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ADC, Zpg),     (ROR, Zpg),     (Illegal, Impl),(PLA, Impl),    (ADC, Imm),     (ROR, Impl),    (Illegal, Impl),(JMP, Ind),     (ADC, Abs),     (ROR, Abs),     (Illegal, Impl),
    (BVS, Rel),     (ADC, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ADC, ZpgX),    (ROR, ZpgX),    (Illegal, Impl),(SEI, Impl),    (ADC, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(ADC, AbsX),    (ROR, AbsX),    (Illegal, Impl),

    (Illegal, Impl),(STA, XInd),    (Illegal, Impl),(Illegal, Impl),(STY, Zpg),     (STA, Zpg),     (STX, Zpg),     (Illegal, Impl),(DEY, Impl),    (Illegal, Impl),(TXA, Impl),    (Illegal, Impl),(STY, Abs),     (STA, Abs),     (STX, Abs),     (Illegal, Impl),
    (BCC, Rel),     (STA, IndY),    (Illegal, Impl),(Illegal, Impl),(STY, ZpgX),    (STA, ZpgX),    (STX, ZpgY),    (Illegal, Impl),(TYA, Impl),    (STA, AbsY),    (TXS, Impl),    (Illegal, Impl),(Illegal, Impl),(STA, AbsX),    (Illegal, Impl),(Illegal, Impl),
    (LDY, Imm),     (LDA, XInd),    (LDX, Imm),     (Illegal, Impl),(LDY, Zpg),     (LDA, Zpg),     (LDX, Zpg),     (Illegal, Impl),(TAY, Impl),    (LDA, Imm),     (TAX, Impl),    (Illegal, Impl),(LDY, Abs),     (LDA, Abs),     (LDX, Abs),     (Illegal, Impl),
    (BCS, Rel),     (LDA, IndY),    (Illegal, Impl),(Illegal, Impl),(LDY, ZpgX),    (LDA, ZpgX),    (LDX, ZpgY),    (Illegal, Impl),(CLV, Impl),    (LDA, AbsY),    (TSX, Impl),    (Illegal, Impl),(LDY, AbsX),    (LDA, AbsX),    (LDX, AbsY),    (Illegal, Impl),
    (CPY, Imm),     (CMP, XInd),    (Illegal, Impl),(Illegal, Impl),(CPY, Zpg),     (CMP, Zpg),     (DEC, Zpg),     (Illegal, Impl),(INY, Impl),    (CMP, Imm),     (DEX, Impl),    (Illegal, Impl),(CPY, Abs),     (CMP, Abs),     (DEC, Abs),     (Illegal, Impl),
    (BNE, Rel),     (CMP, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(CMP, ZpgX),    (DEC, ZpgX),    (Illegal, Impl),(CLD, Impl),    (CMP, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(CMP, AbsX),    (DEC, AbsX),    (Illegal, Impl),
    (CPX, Imm),     (SBC, XInd),    (Illegal, Impl),(Illegal, Impl),(CPX, Zpg),     (SBC, Zpg),     (INC, Zpg),     (Illegal, Impl),(INX, Impl),    (SBC, Imm),     (NOP, Impl),    (Illegal, Impl),(CPX, Abs),     (SBC, Abs),     (INC, Abs),     (Illegal, Impl),
    (BEQ, Rel),     (SBC, IndY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(SBC, ZpgX),    (INC, ZpgX),    (Illegal, Impl),(SED, Impl),    (SBC, AbsY),    (Illegal, Impl),(Illegal, Impl),(Illegal, Impl),(SBC, AbsX),    (INC, AbsX),    (Illegal, Impl),
];

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Instruction {
    opcode: Opcode,
    opcode_byte: u8,
    operand: Operand,
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:02X} {:?}", self.opcode_byte, self.operand))
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} {} {}", self.opcode, self.operand, self.operand.to_addr_mode()))
    }
}

impl Instruction {
    pub fn new(opcode: Opcode, operand: Operand, opcode_byte: u8) -> Self {
        return Self{opcode, operand, opcode_byte}
    }

    pub fn opcode(&self) -> Opcode {
        return self.opcode
    }

    pub fn operand(&self) -> Operand {
        return self.operand
    }
}
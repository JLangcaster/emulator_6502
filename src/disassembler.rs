use std::fmt::Display;
use crate::instructions::{Opcode, AddrMode, Operand, INST_TABLE, Instruction};

pub struct Decoder {
    data: Vec<u8>,
    pointer: usize,
}

impl Decoder {
    pub fn from_file(path: impl AsRef<std::path::Path>) -> Self {
        return Self {
            data: std::fs::read(path).expect("Couldn't open file"),
            pointer: 0,
        }
    }

    pub fn read_byte(&mut self) -> Result<u8, std::io::Error> {
        if self.pointer >= self.data.len() {
            return Err(std::io::Error::from(std::io::ErrorKind::UnexpectedEof))
        }
        let byte = self.data[self.pointer];
        self.pointer += 1;
        return Ok(byte)
    }

    pub fn read_word(&mut self) -> Result<u16, std::io::Error> {
        let word_lo = self.read_byte()?;
        let word_hi = self.read_byte()?;
        return Ok(u16::from_le_bytes([word_lo, word_hi]));
    }

    pub fn set_pointer(&mut self, pointer: usize) {
        self.pointer = pointer;
    }

    pub fn read_instruction(&mut self) -> Result<Instruction, std::io::Error> {
        let opcode_byte = self.read_byte()?;

        let (opcode, addr_mode) = INST_TABLE[opcode_byte as usize];

        let operand = match addr_mode {
            AddrMode::Abs => Operand::Abs(self.read_word()?),
            AddrMode::AbsX => Operand::AbsX(self.read_word()?),
            AddrMode::AbsY => Operand::AbsY(self.read_word()?),
            AddrMode::Imm => Operand::Imm(self.read_byte()?),
            AddrMode::Impl => Operand::Impl,
            AddrMode::Ind => Operand::Ind(self.read_word()?),
            AddrMode::XInd => Operand::XInd(self.read_byte()?),
            AddrMode::IndY => Operand::IndY(self.read_byte()?),
            AddrMode::Rel => Operand::Rel(i8::from_le_bytes([self.read_byte()?])),
            AddrMode::Zpg => Operand::Zpg(self.read_byte()?),
            AddrMode::ZpgX => Operand::ZpgX(self.read_byte()?),
            AddrMode::ZpgY => Operand::ZpgY(self.read_byte()?)
        };

        return Ok(Instruction::new(opcode, operand, opcode_byte))
    }

    pub fn disassemble(&mut self) -> Result<Vec<(usize, Instruction)>, (Vec<(usize, Instruction)>, std::io::Error)> {
        let mut stream = Vec::new();

        while self.pointer < self.data.len() {
            let curr_pointer = self.pointer;
            let next_instruction = self.read_instruction();
            match next_instruction {
                Ok(inst) => stream.push((curr_pointer, inst)),
                Err(e) => return Err((stream, e))
            };
        }

        return Ok(stream);
    }
}
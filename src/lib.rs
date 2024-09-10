use std::io::{self, Read, Write};

const MEMORY_SIZE: usize = 30_000;

pub struct Context<I: Read, O: Write> {
    pub output: O,
    pub input: I,
}

struct OpImpl<I: Read, O: Write> {
    op: fn(arg: isize, context: &mut Context<I, O>, memory: *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error>,
    arg: isize,
}

impl<I: Read, O: Write> Clone for OpImpl<I, O> {
    fn clone(&self) -> Self {
        Self { op: self.op, arg: self.arg }
    }
}

fn dispatch<I: Read, O: Write>(context: &mut Context<I, O>, memory: *mut u8, dp: usize, program: *const OpImpl<I, O>, offset: isize) -> Result<(), io::Error> {
    let program = unsafe { program.offset(offset) };
    let op: &OpImpl<I, O> = unsafe { &*program };

    (op.op)(op.arg, context, memory, dp, program)
}

#[cold]
#[inline(never)]
fn out_of_bounds() -> Result<(), io::Error> {
    Err(io::Error::new(io::ErrorKind::InvalidInput, "out of bounds"))
}

fn op_halt<I: Read, O: Write>(_arg: isize, _context: &mut Context<I, O>, _memory:  *mut u8, _dp: usize, _program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    Ok(())
}

fn op_inc_dp<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    dispatch(context, memory, dp.wrapping_add_signed(arg), program, 1)
}

fn op_inc_memory<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    let ptr: &mut u8 = unsafe { &mut *memory.add(dp) };
    *ptr = ptr.wrapping_add_signed(arg as i8);

    dispatch(context, memory, dp, program, 1)
}

fn op_set_zero<I: Read, O: Write>(_arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    let ptr: &mut u8 = unsafe { &mut *memory.add(dp) };
    *ptr = 0;

    dispatch(context, memory, dp, program, 1)
}

fn op_jmp_zero<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    dispatch(context, memory, dp, program, if unsafe { *memory.add(dp) } == 0 { arg } else { 1 })
}

fn op_jmp_non_zero<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    dispatch(context, memory, dp, program, if unsafe { *memory.add(dp) } != 0 { arg } else { 1 })
}

fn op_write<I: Read, O: Write>(_arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    write!(context.output, "{}", unsafe { *memory.add(dp) } as char)?;
    dispatch(context, memory, dp, program, 1)
}

fn op_read<I: Read, O: Write>(_arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const OpImpl<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    let ptr = unsafe { &mut *memory.add(dp) };

    match context.input.read_exact(::std::slice::from_mut(ptr)) {
        Ok(_) => { /* pass */ },
        Err(err) => {
            if err.kind() == io::ErrorKind::UnexpectedEof {
                *ptr = 0;
            } else {
                return Err(err);
            }
        }
    }

    dispatch(context, memory, dp, program, 1)
}

#[derive(Debug, PartialEq, Clone)]
pub enum Op {
    IncDp(isize),
    IncMemory(isize),
    SetZero,
    Write,
    Read,
}

impl From<u8> for Op {
    fn from(ch: u8) -> Self {
        match ch {
            b'<' => Op::IncDp(-1),
            b'>' => Op::IncDp(1),
            b'+' => Op::IncMemory(1),
            b'-' => Op::IncMemory(-1),
            b'.' => Op::Write,
            b',' => Op::Read,
            _ => unreachable!("unexpected op: {}", ch),
        }
    }
}

impl Op {
    fn to_impl<I: Read, O: Write>(self) -> OpImpl<I, O> {
        match self {
            Self::IncDp(arg) => OpImpl { op: op_inc_dp, arg },
            Self::IncMemory(arg) => OpImpl { op: op_inc_memory, arg },
            Self::SetZero => OpImpl { op: op_set_zero, arg: 0 },
            Self::Write => OpImpl { op: op_write, arg: 0 },
            Self::Read => OpImpl { op: op_read, arg: 0 },
        }
    }

    fn try_merge(&mut self, other: &Self) -> bool {
        match (self, other) {
            (Self::IncDp(ref mut a), Self::IncDp(b)) => {
                *a += b;
                true
            },
            (Self::IncMemory(ref mut a), Self::IncMemory(b)) => {
                *a += b;
                true
            },
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnexpectedChar(u8),
    UnexpectedEnd,
}

#[derive(Debug, PartialEq)]
pub enum Parsed {
    Block(Vec<Op>),
    Loop(Vec<Parsed>),
    Once(Vec<Parsed>),
}

impl TryFrom<&[u8]> for Parsed {
    type Error = ParseError;

    fn try_from(program: &[u8]) -> Result<Self, Self::Error> {
        Parsed::parse(program).map(|blocks| Self::Once(blocks).rewrite())
    }
}

impl Parsed {
    fn parse(program: &[u8]) -> Result<Vec<Parsed>, ParseError> {
        let mut blocks = vec! [];
        let mut i = 0;

        while i < program.len() {
            match program[i] {
                b'<' | b'>' | b'+' | b'-' | b'.' | b',' => {
                    if let Some(Parsed::Block(ref mut last_block)) = blocks.last_mut() {
                        last_block.push(Op::from(program[i]));
                    } else {
                        blocks.push(Parsed::Block(vec! [Op::from(program[i])]));
                    }
                    i += 1;
                },
                b'[' => {
                    let ends_at = Self::loop_slice_at(&program[i + 1..])? + i;
                    let sub_blocks = Self::parse(&program[i + 1..ends_at])?;

                    blocks.push(Parsed::Loop(sub_blocks));

                    i = ends_at + 1;
                },
                b']' => { return Err(ParseError::UnexpectedChar(b']')) },
                _ => { i += 1; },
            }
        }

        Ok(blocks)
    }

    fn loop_slice_at(program: &[u8]) -> Result<usize, ParseError> {
        let mut depth = 1;
        let mut i = 0;

        while depth > 0 {
            match program.get(i) {
                Some(b'[') => { depth += 1; },
                Some(b']') => { depth -= 1; },
                Some(_) => { /* pass */ },
                None => { return Err(ParseError::UnexpectedEnd); },
            }

            i += 1;
        }

        Ok(i)
    }

    fn is_single_op(&self, predicate: impl Fn(&Op) -> bool) -> bool {
        match self {
            Self::Block(ops) => ops.len() == 1 && predicate(&ops[0]),
            _ => false,
        }
    }

    fn merge_consecutive_ops(ops: &[Op]) -> Vec<Op> {
        let mut merged: Vec<Op> = vec! [];

        for op in ops {
            if let Some(last_merged) = merged.last_mut() {
                if !last_merged.try_merge(op) {
                    merged.push(op.clone());
                }
            } else {
                merged.push(op.clone());
            }
        }

        merged
    }

    fn rewrite(self) -> Self {
        match self {
            Self::Block(ops) => Self::Block(Self::merge_consecutive_ops(&ops)),
            Self::Loop(sub_blocks) => {
                let new_sub_blocks = sub_blocks.into_iter().map(Self::rewrite).collect::<Vec<Parsed>>();

                if new_sub_blocks.len() == 1 && (new_sub_blocks[0].is_single_op(|op| Op::SetZero.eq(op) || Op::IncMemory(-1).eq(op))) {
                    Self::Block(vec! [Op::SetZero])
                } else {
                    Self::Loop(new_sub_blocks)
                }
            },
            Self::Once(blocks) => Self::Once(blocks.into_iter().map(Self::rewrite).collect())
        }
    }
}

pub struct Compiled<I: Read, O: Write> {
    ops: Vec<OpImpl<I, O>>,
}

impl<I: Read, O: Write> From<Parsed> for Compiled<I, O> {
    fn from(parsed: Parsed) -> Self {
        let mut ops = Self::compile(parsed);
        ops.push(OpImpl { op: op_halt, arg: 0 });

        Self { ops }
    }
}

impl<I: Read, O: Write> Compiled<I, O> {
    fn compile(parsed: Parsed) -> Vec<OpImpl<I, O>> {
        let mut ops = vec! [];

        match parsed {
            Parsed::Block(block) => {
                ops.extend(block.into_iter().map(Op::to_impl));
            },
            Parsed::Loop(sub_blocks) => {
                let mut loop_ops = vec! [];

                for sub_block in sub_blocks {
                    loop_ops.extend(Self::compile(sub_block));
                }

                ops.push(OpImpl { op: op_jmp_zero, arg: loop_ops.len() as isize + 2 });
                ops.extend_from_slice(&loop_ops);
                ops.push(OpImpl { op: op_jmp_non_zero, arg: -(loop_ops.len() as isize) });
            },
            Parsed::Once(blocks) => {
                for block in blocks {
                    ops.extend(Self::compile(block));
                }
            },
        }

        ops
    }
}

pub fn execute<I: Read, O: Write>(context: &mut Context<I, O>, block: &Compiled<I, O>)  -> Result<(), io::Error> {
    let mut memory = vec! [0; 30_000];

    dispatch(
        context,
        memory.as_mut_ptr(),
        0,
        block.ops.as_ptr(),
        0
    )
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    use super::*;

    impl Context<Cursor<Vec<u8>>, Vec<u8>> {
        fn with_input(input: &[u8]) -> Self {
            Self {
                output: Vec::new(),
                input: Cursor::new(input.to_vec())
            }
        }
    }

    #[test]
    fn rewrite_consequitive_ops() {
        let program = b"++><>--";

        assert_eq!(
            Parsed::try_from(&program[..]).expect("could not parse program"),
            Parsed::Once(vec! [
                Parsed::Block(vec! [Op::IncMemory(2), Op::IncDp(1), Op::IncMemory(-2)])
            ])
        );
    }

    #[test]
    fn rewrite_set_zero_loop() {
        let program = b">[[+--]]";

        assert_eq!(
            Parsed::try_from(&program[..]).expect("could not parse program"),
            Parsed::Once(vec! [
                Parsed::Block(vec! [Op::IncDp(1)]),
                Parsed::Block(vec! [Op::SetZero])
            ])
        );
    }

    #[test]
    fn hello_world() {
        let program = b">>+<--[[<++>->-->+++>+<<<]-->++++]<<.<<-.<<..+++.>.<<-.>.+++.------.>>-.<+.>>.";
        let parsed = Parsed::try_from(&program[..]).expect("could not parse program");
        let block = Compiled::from(parsed);
        let mut context = Context::with_input(b"");

        execute(&mut context, &block).expect("could not execute program");

        assert_eq!(context.output, b"Hello World!\n");
    }

    #[test]
    fn quick_sort() {
        let program = b">>+>>>>>,[>+>>,]>+[--[+<<<-]<[<+>-]<[<[->[<<<+>>>>+<-]<<[>>+>[->]<<[<]<-]>]>>>+<[[-]<[>+<-]<]>[[>>>]+<<<-<[<<[<<<]>>+>[>>>]<-]<<[<<<]>[>>[>>>]<+<<[<<<]>-]]+<<<]+[->>>]>>]>>[.>>>]";
        let parsed = Parsed::try_from(&program[..]).expect("could not parse program");
        let block = Compiled::from(parsed);
        let mut context = Context::with_input(b"2635789014");

        execute(&mut context, &block).expect("could not execute program");

        assert_eq!(context.output, b"0123456789");
    }
}

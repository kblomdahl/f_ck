use std::{io::{self, Read, Write}, iter::Peekable};

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
    fn to_impl<I: Read, O: Write>(&self) -> OpImpl<I, O> {
        match self {
            Self::IncDp(arg) => OpImpl { op: op_inc_dp, arg: *arg },
            Self::IncMemory(arg) => OpImpl { op: op_inc_memory, arg: *arg },
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
    Ops(Vec<Op>),
    Loop(Vec<Parsed>),
    Once(Vec<Parsed>),
}

impl TryFrom<&[u8]> for Parsed {
    type Error = ParseError;

    fn try_from(program: &[u8]) -> Result<Self, Self::Error> {
        let mut iter = program.iter().copied().peekable();
        let blocks = Self::parse_blocks_while(&mut iter, |ch| ch != None)?;
        let mut parsed = Self::Once(blocks);
        parsed.rewrite();

        Ok(parsed)
    }
}

impl Parsed {
    fn parse_ops(program: &mut Peekable<impl Iterator<Item=u8>>) -> Result<Parsed, ParseError> {
        let mut ops = vec! [];

        while let Some(ch) = program.next_if(|ch| !matches!(ch, b'[' | b']')) {
            match ch {
                b'<' | b'>' | b'+' | b'-' | b'.' | b',' => ops.push(Op::from(ch)),
                _ => { /* pass */ },
            }
        }

        Ok(Parsed::Ops(ops))
    }

    fn parse_block(program: &mut Peekable<impl Iterator<Item=u8>>) -> Result<Parsed, ParseError> {
        match program.peek() {
            Some(b'[') => Self::parse_loop(program),
            Some(b']') => Err(ParseError::UnexpectedChar(b']')),
            Some(_) => Self::parse_ops(program),
            None => Err(ParseError::UnexpectedEnd),
        }
    }

    fn parse_blocks_while(program: &mut Peekable<impl Iterator<Item=u8>>, predicate: impl Fn(Option<&u8>) -> bool) -> Result<Vec<Parsed>, ParseError> {
        let mut blocks = vec! [];

        while predicate(program.peek()) {
            blocks.push(Self::parse_block(program)?);
        }

        Ok(blocks)
    }

    fn parse_loop(program: &mut Peekable<impl Iterator<Item=u8>>) -> Result<Parsed, ParseError> {
        assert_eq!(program.next(), Some(b'['));

        let blocks = Self::parse_blocks_while(program, |ch| ch != Some(&b']'))?;
        let _ = program.next();  // this must be b']'

        Ok(Parsed::Loop(blocks))
    }

    fn is_single_op(&self, predicate: impl Fn(&Op) -> bool) -> bool {
        match self {
            Self::Ops(ops) => ops.len() == 1 && predicate(&ops[0]),
            _ => false,
        }
    }

    fn merge_consecutive_ops(ops: &mut Vec<Op>) {
        let len = ops.len();
        let mut read_at = 1;
        let mut merge_at = 0;

        while read_at < len {
            debug_assert!(merge_at < read_at);

            let to_try_merge = ops[read_at].clone();

            if ops[merge_at].try_merge(&to_try_merge) {
                read_at += 1;
            } else {
                ops[merge_at + 1] = ops[read_at].clone();

                merge_at += 1;
                read_at += 1;
            }
        }

        ops.truncate(merge_at + 1);
    }

    fn rewrite(&mut self) {
        match self {
            Self::Ops(ops) => Self::merge_consecutive_ops(ops),
            Self::Loop(blocks) => {
                blocks.iter_mut().for_each(Self::rewrite);

                if blocks.len() == 1 && (blocks[0].is_single_op(|op| Op::SetZero.eq(op) || Op::IncMemory(-1).eq(op))) {
                    *self = Self::Ops(vec! [Op::SetZero])
                }
            },
            Self::Once(blocks) => blocks.iter_mut().for_each(Self::rewrite),
        }
    }
}

pub struct Compiled<I: Read, O: Write> {
    ops: Vec<OpImpl<I, O>>,
}

impl<I: Read, O: Write> From<&Parsed> for Compiled<I, O> {
    fn from(parsed: &Parsed) -> Self {
        let mut ops = vec! [];

        Self::compile(parsed, &mut ops);
        ops.push(OpImpl { op: op_halt, arg: 0 });

        Self { ops }
    }
}

impl<I: Read, O: Write> Compiled<I, O> {
    fn compile(parsed: &Parsed, ops: &mut Vec<OpImpl<I, O>>) {
        match parsed {
            Parsed::Ops(block) => {
                ops.extend(block.iter().map(Op::to_impl));
            },
            Parsed::Loop(blocks) => {
                let starts_at = ops.len();

                ops.push(OpImpl { op: op_jmp_zero, arg: 0 });

                for block in blocks {
                    Self::compile(block, ops);
                }

                let loop_len = ops.len() - starts_at;

                ops[starts_at].arg = loop_len as isize + 1;
                ops.push(OpImpl { op: op_jmp_non_zero, arg: -(loop_len as isize - 1) });
            },
            Parsed::Once(blocks) => {
                for block in blocks {
                    Self::compile(block, ops);
                }
            },
        }
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
    fn malformed() {
        assert_eq!(Parsed::try_from(b"[".as_slice()), Err(ParseError::UnexpectedEnd));
        assert_eq!(Parsed::try_from(b"]".as_slice()), Err(ParseError::UnexpectedChar(b']')));
    }

    #[test]
    fn rewrite_consequitive_ops() {
        let program = b"++><>--";

        assert_eq!(
            Parsed::try_from(&program[..]).expect("could not parse program"),
            Parsed::Once(vec! [
                Parsed::Ops(vec! [Op::IncMemory(2), Op::IncDp(1), Op::IncMemory(-2)])
            ])
        );
    }

    #[test]
    fn rewrite_set_zero_loop() {
        let program = b">[[+--]]";

        assert_eq!(
            Parsed::try_from(&program[..]).expect("could not parse program"),
            Parsed::Once(vec! [
                Parsed::Ops(vec! [Op::IncDp(1)]),
                Parsed::Ops(vec! [Op::SetZero])
            ])
        );
    }

    #[test]
    fn hello_world() {
        let program = b">>+<--[[<++>->-->+++>+<<<]-->++++]<<.<<-.<<..+++.>.<<-.>.+++.------.>>-.<+.>>.";
        let parsed = Parsed::try_from(&program[..]).expect("could not parse program");
        let block = Compiled::from(&parsed);
        let mut context = Context::with_input(b"");

        execute(&mut context, &block).expect("could not execute program");

        assert_eq!(context.output, b"Hello World!\n");
    }

    #[test]
    fn quick_sort() {
        let program = b">>+>>>>>,[>+>>,]>+[--[+<<<-]<[<+>-]<[<[->[<<<+>>>>+<-]<<[>>+>[->]<<[<]<-]>]>>>+<[[-]<[>+<-]<]>[[>>>]+<<<-<[<<[<<<]>>+>[>>>]<-]<<[<<<]>[>>[>>>]<+<<[<<<]>-]]+<<<]+[->>>]>>]>>[.>>>]";
        let parsed = Parsed::try_from(&program[..]).expect("could not parse program");
        let block = Compiled::from(&parsed);
        let mut context = Context::with_input(b"2635789014");

        execute(&mut context, &block).expect("could not execute program");

        assert_eq!(context.output, b"0123456789");
    }
}

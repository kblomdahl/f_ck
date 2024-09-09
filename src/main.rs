use std::io::{self, Read, Stdin, Stdout, Write};

const MEMORY_SIZE: usize = 30_000;

struct Context<I: Read, O: Write> {
    output: O,
    input: I,
}

impl Default for Context<Stdin, Stdout> {
    fn default() -> Self {
        Self {
            output: io::stdout(),
            input: io::stdin(),
        }
    }
}

struct Op<I: Read, O: Write> {
    op: fn(arg: isize, context: &mut Context<I, O>, memory: *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error>,
    arg: isize,
}

impl<I: Read, O: Write> Clone for Op<I, O> {
    fn clone(&self) -> Self {
        Self { op: self.op, arg: self.arg }
    }
}

fn dispatch<I: Read, O: Write>(context: &mut Context<I, O>, memory: *mut u8, dp: usize, program: *const Op<I, O>, offset: isize) -> Result<(), io::Error> {
    let program = unsafe { program.offset(offset) };
    let op: &Op<I, O> = unsafe { &*program };

    (op.op)(op.arg, context, memory, dp, program)
}

#[cold]
#[inline(never)]
fn out_of_bounds() -> Result<(), io::Error> {
    Err(io::Error::new(io::ErrorKind::InvalidInput, "out of bounds"))
}

fn op_unexpected_op<I: Read, O: Write>(_arg: isize, _context: &mut Context<I, O>, _memory:  *mut u8, _dp: usize, _program: *const Op<I, O>) -> Result<(), io::Error> {
    unreachable!("unexpected op")
}

fn op_halt<I: Read, O: Write>(_arg: isize, _context: &mut Context<I, O>, _memory:  *mut u8, _dp: usize, _program: *const Op<I, O>) -> Result<(), io::Error> {
    Ok(())
}

fn op_inc_dp<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
    dispatch(context, memory, dp.wrapping_add_signed(arg), program, 1)
}

fn op_inc_memory<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    let ptr: &mut u8 = unsafe { &mut *memory.add(dp) };
    *ptr = ptr.wrapping_add_signed(arg as i8);

    dispatch(context, memory, dp, program, 1)
}

fn op_jmp_zero<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    dispatch(context, memory, dp, program, if unsafe { *memory.add(dp) } == 0 { arg } else { 1 })
}

fn op_jmp_non_zero<I: Read, O: Write>(arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    dispatch(context, memory, dp, program, if unsafe { *memory.add(dp) } != 0 { arg } else { 1 })
}

fn op_write<I: Read, O: Write>(_arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
    if dp >= MEMORY_SIZE {
        return out_of_bounds();
    }

    write!(context.output, "{}", unsafe { *memory.add(dp) } as char)?;
    dispatch(context, memory, dp, program, 1)
}

fn op_read<I: Read, O: Write>(_arg: isize, context: &mut Context<I, O>, memory:  *mut u8, dp: usize, program: *const Op<I, O>) -> Result<(), io::Error> {
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

struct Block<I: Read, O: Write> {
    ops: Vec<Op<I, O>>,
}

impl<I: Read, O: Write> Block<I, O> {
    fn new(program: &[u8]) -> Self {
        let mut ops = Self::parse(program);
        ops.push(Op { op: op_halt, arg: 0 });

        Self { ops }
    }

    fn parse(program: &[u8]) -> Vec<Op<I, O>> {
        let mut ops = vec! [];
        let mut i = 0;

        while i < program.len() {
            match program[i] {
                b'<' | b'>' | b'+' | b'-' | b'.' | b',' => {
                    ops.push(Self::op_from_byte(program[i]));
                    i += 1;
                },
                b'[' => {
                    let ends_at = Self::loop_slice_at(&program[i + 1..]) + i;
                    let sub_ops = Self::parse(&program[i + 1..ends_at]);

                    ops.push(Op { op: op_jmp_zero, arg: (sub_ops.len() + 2) as isize });
                    ops.extend_from_slice(&sub_ops);
                    ops.push(Op { op: op_jmp_non_zero, arg: -(sub_ops.len() as isize) });

                    i = ends_at + 1;
                },
                b']' => { unreachable!("unexpected ] at {}", i) },
                _ => { i += 1; },
            }
        }

        ops
    }

    fn op_from_byte(byte: u8) -> Op<I, O> {
        match byte {
            b'<' => Op { op: op_inc_dp, arg: -1 },
            b'>' => Op { op: op_inc_dp, arg: 1 },
            b'+' => Op { op: op_inc_memory, arg: 1 },
            b'-' => Op { op: op_inc_memory, arg: -1 },
            b'.' => Op { op: op_write, arg: 0 },
            b',' => Op { op: op_read, arg: 0 },
            _ => Op { op: op_unexpected_op, arg: 0 },
        }
    }

    fn loop_slice_at(program: &[u8]) -> usize {
        let mut depth = 1;
        let mut i = 0;

        while depth > 0 {
            match program[i] {
                b'[' => { depth += 1; },
                b']' => { depth -= 1; },
                _ => { /* pass */ },
            }

            i += 1;
        }

        i
    }
}

fn execute<I: Read, O: Write>(context: &mut Context<I, O>, block: &Block<I, O>)  -> Result<(), io::Error> {
    let mut memory = vec! [0; 30_000];

    dispatch(
        context,
        memory.as_mut_ptr(),
        0,
        block.ops.as_ptr(),
        0
    )
}

fn main() -> Result<(), io::Error> {
    for arg in std::env::args().skip(1) {
        let program = std::fs::read(&arg)?;
        let block: Block<Stdin, Stdout> = Block::new(&program[..]);

        execute(&mut Context::default(), &block)?;
    }

    Ok(())
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
    fn hello_world() -> Result<(), io::Error> {
        let program = b">>+<--[[<++>->-->+++>+<<<]-->++++]<<.<<-.<<..+++.>.<<-.>.+++.------.>>-.<+.>>.";
        let block = Block::new(&program[..]);
        let mut context = Context::with_input(b"");

        execute(&mut context, &block)?;

        assert_eq!(context.output, b"Hello World!\n");
        Ok(())
    }

    #[test]
    fn quick_sort() -> Result<(), io::Error> {
        let program = b">>+>>>>>,[>+>>,]>+[--[+<<<-]<[<+>-]<[<[->[<<<+>>>>+<-]<<[>>+>[->]<<[<]<-]>]>>>+<[[-]<[>+<-]<]>[[>>>]+<<<-<[<<[<<<]>>+>[>>>]<-]<<[<<<]>[>>[>>>]<+<<[<<<]>-]]+<<<]+[->>>]>>]>>[.>>>]";
        let block = Block::new(&program[..]);
        let mut context = Context::with_input(b"2635789014");

        execute(&mut context, &block)?;

        assert_eq!(context.output, b"0123456789");
        Ok(())
    }
}

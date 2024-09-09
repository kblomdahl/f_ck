use std::io::{self, Read, Stdin, Stdout, Write};

struct Context<I: Read, O: Write> {
    output: O,
    input: I,
    memory: Vec<u8>,
    dp: usize,
}

impl Default for Context<Stdin, Stdout> {
    fn default() -> Self {
        Self {
            output: io::stdout(),
            input: io::stdin(),
            memory: vec! [0; 30_000],
            dp: 0,
        }
    }
}

#[derive(Debug, PartialEq)]
enum Block {
    Pure(Vec<u8>),
    Loop(Vec<Block>),
}

impl Block {
    fn parse(program: &[u8]) -> Vec<Self> {
        let mut blocks: Vec<Block> = vec! [];
        let mut i = 0;

        while i < program.len() {
            match program[i] {
                b'<' | b'>' | b'+' | b'-' | b'.' | b',' => {
                    if let Some(Self::Pure(block)) = blocks.last_mut() {
                        block.push(program[i]);
                    } else {
                        blocks.push(Self::Pure(vec! [program[i]]));
                    }

                    i += 1;
                },
                b'[' => {
                    let ends_at = Self::loop_slice_at(&program[i + 1..]) + i;

                    blocks.push(Self::Loop(Self::parse(&program[i + 1..ends_at])));
                    i = ends_at + 1;
                },
                b']' => { unreachable!("unexpected ] at {}", i) },
                _ => { i += 1; },
            }
        }

        blocks
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

    fn execute<I: Read, O: Write>(&self, context: &mut Context<I, O>) -> Result<(), io::Error> {
        match self {
            Self::Pure(block) => {
                for &op in block {
                    match op {
                        b'>' => { context.dp += 1; },
                        b'<' => { context.dp -= 1; },
                        b'+' => { context.memory[context.dp] = context.memory[context.dp].wrapping_add(1); },
                        b'-' => { context.memory[context.dp] = context.memory[context.dp].wrapping_sub(1); },
                        b'.' => { write!(context.output, "{}", context.memory[context.dp] as char)?; },
                        b',' => {
                            match context.input.read_exact(&mut context.memory[context.dp..context.dp + 1]) {
                                Ok(_) => { /* pass */ },
                                Err(err) => {
                                    if err.kind() == io::ErrorKind::UnexpectedEof {
                                        context.memory[context.dp] = 0;
                                    } else {
                                        return Err(err);
                                    }
                                }
                            }
                        },
                        _ => { unreachable!("unexpected op: {}", op as char) },
                    }
                }
            },
            Self::Loop(blocks) => {
                while context.memory[context.dp] != 0 {
                    for block in blocks {
                        block.execute(context)?;
                    }
                }
            },
        }

        Ok(())
    }
}

fn execute(program: &[u8])  -> Result<(), io::Error> {
    let blocks = Block::parse(program);
    let mut context = Context::default();

    for block in blocks {
        block.execute(&mut context)?
    }

    Ok(())
}

fn main() -> Result<(), io::Error> {
    for arg in std::env::args().skip(1) {
        let program = std::fs::read(&arg)?;

        execute(&program)?;
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
                input: Cursor::new(input.to_vec()),
                memory: vec! [0; 30_000],
                dp: 0,
            }
        }
    }

    #[test]
    fn hello_world() -> Result<(), io::Error> {
        let program = b">>+<--[[<++>->-->+++>+<<<]-->++++]<<.<<-.<<..+++.>.<<-.>.+++.------.>>-.<+.>>.";
        let blocks = Block::parse(&program[..]);

        assert_eq!(
            blocks,
            vec! [
                Block::Pure(vec! [b'>', b'>', b'+', b'<', b'-', b'-']),
                Block::Loop(vec! [
                    Block::Loop(vec! [
                        Block::Pure(vec! [b'<', b'+', b'+', b'>', b'-', b'>', b'-', b'-', b'>', b'+', b'+', b'+', b'>', b'+', b'<', b'<', b'<']),
                    ]),
                    Block::Pure(vec! [b'-', b'-', b'>', b'+', b'+', b'+', b'+']),
                ]),
                Block::Pure(vec ![b'<', b'<', b'.', b'<' , b'<', b'-', b'.', b'<', b'<', b'.', b'.', b'+', b'+', b'+', b'.', b'>', b'.', b'<', b'<', b'-', b'.', b'>', b'.', b'+', b'+', b'+', b'.', b'-', b'-', b'-', b'-', b'-', b'-', b'.', b'>', b'>', b'-', b'.', b'<', b'+', b'.', b'>', b'>', b'.']),
            ]
        );

        let mut context = Context::with_input(b"");

        for block in blocks {
            block.execute(&mut context)?;
        }

        assert_eq!(context.output, b"Hello World!\n");
        Ok(())
    }

    #[test]
    fn quick_sort() -> Result<(), io::Error> {
        let program = b">>+>>>>>,[>+>>,]>+[--[+<<<-]<[<+>-]<[<[->[<<<+>>>>+<-]<<[>>+>[->]<<[<]<-]>]>>>+<[[-]<[>+<-]<]>[[>>>]+<<<-<[<<[<<<]>>+>[>>>]<-]<<[<<<]>[>>[>>>]<+<<[<<<]>-]]+<<<]+[->>>]>>]>>[.>>>]";
        let blocks = Block::parse(&program[..]);
        let mut context = Context::with_input(b"2635789014");

        for block in blocks {
            block.execute(&mut context)?;
        }

        assert_eq!(context.output, b"0123456789");
        Ok(())
    }
}

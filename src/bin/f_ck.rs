use f_ck::*;
use std::io;

fn main() -> Result<(), io::Error> {
    let mut context = Context {
        output: io::stdout(),
        input: io::stdin(),
    };

    for arg in std::env::args().skip(1) {
        let program = std::fs::read(&arg)?;

        match Parsed::try_from(&program[..]) {
            Ok(parsed) => {
                execute(&mut context, &Compiled::from(parsed))?;
            },
            Err(err) => {
                eprintln!("{}: {:?}", arg, err);
            }
        }
    }

    Ok(())
}

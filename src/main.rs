use std::io;
use std::io::Write;
use pawer_core::{print_comms,print_state};

// A simple top-level, mostly used for debbuging
fn main() -> io::Result<()> {

    loop {
        print!(" > ");
        io::stdout().flush().unwrap();
        
        // get stdin 
        let mut buffer = String::new();
        let stdin = io::stdin();
        stdin.read_line(&mut buffer)?;

        // send
        print_comms(&buffer);

        // print
        print_state();
    }

}
// 
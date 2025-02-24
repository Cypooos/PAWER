use std::io;
use std::io::Write;
use pawer::{definitions::GlobalContext,print_comms};


// A simple top-level, mostly used for debbuging
fn main() -> io::Result<()> {

    let mut pa = GlobalContext::new();
    pa.load_prelude();

    loop {
        print!(" > ");
        io::stdout().flush().unwrap();
        
        // get stdin 
        let mut buffer = String::new();
        let stdin = io::stdin();
        stdin.read_line(&mut buffer)?;

        // send
        print_comms(&mut pa,&buffer);

        // print
        println!("{}",pa);
    }

}
// 
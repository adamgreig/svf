use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let contents = fs::read_to_string(filename).unwrap();
    for cmd in svf::parse_iter(&contents) {
        match cmd {
            Ok(cmd) => println!("{}", cmd),
            Err(e)  => eprintln!("Error parsing: {}", e),
        }
    }
}

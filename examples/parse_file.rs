use svf::parse;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let contents = fs::read_to_string(filename).unwrap();
    match parse(&contents) {
        Ok(commands) => for cmd in commands.iter() {
            println!("{}", cmd);
        },
        Err(e) => eprintln!("Error parsing: {}", e),
    }
}

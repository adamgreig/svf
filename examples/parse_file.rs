use svf::parse;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let contents = fs::read_to_string(filename).unwrap();
    let commands = match parse(&contents) {
        Ok(commands) => commands,
        Err(e)       => panic!("Error parsing: {}", e),
    };
    for cmd in commands.iter() {
        println!("{}", cmd);
    }
}

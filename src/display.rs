#![allow(clippy::write_with_newline)]

use std::fmt;

use super::{
    Command,
    PIOMapDirection,
    Pattern,
    RunClock,
    RunTestForm,
    RunTestTime,
    State,
    TRSTMode,
    VectorChar
};

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Display for VectorChar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.length)?;
        // Since the patterns are often long, and SVF requires lines do not exceed 256
        // characters, go to some effort to wrap long lines and format them neatly.
        const BYTES_PER_LINE: usize = 36;
        let mut break_next = false;
        for (name, data) in [
            ("TDI", &self.tdi),
            ("TDO", &self.tdo),
            ("MASK", &self.mask),
            ("SMASK", &self.smask)
        ].iter() {
            if let Some(data) = data {
                if break_next {
                    write!(f, "\n ")?;
                    break_next = false;
                }
                let skip = data.iter().rev().position(|&x| x != 0).unwrap_or(data.len() - 1);
                let data = &data[..data.len() - skip];
                write!(f, " {} (", name)?;
                for (idx, byte) in data.iter().rev().enumerate() {
                    if data.len() > BYTES_PER_LINE && idx % BYTES_PER_LINE == 0 {
                        write!(f, "\n    ")?;
                    }
                    write!(f, "{:02X}", byte)?;
                }
                write!(f, ")")?;
                if data.len() > BYTES_PER_LINE {
                    break_next = true;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for PIOMapDirection {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_ascii_uppercase())
    }
}

impl fmt::Display for RunClock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Display for TRSTMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{:?}", self).to_ascii_uppercase())
    }
}

impl fmt::Display for RunTestTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:E} SEC", self.min)?;
        if let Some(max) = self.max {
            write!(f, " MAXIMUM {:E} SEC", max)?;
        }
        Ok(())
    }
}

impl fmt::Display for RunTestForm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RunTestForm::Clocked { run_count, run_clk, time } => {
                write!(f, "{} {}", run_count, run_clk)?;
                if let Some(t) = time {
                    write!(f, " {}", t)?;
                }
            },
            RunTestForm::Timed(t) => {
                write!(f, "{}", t)?;
            },
        }
        Ok(())
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::EndDR(state) => write!(f, "ENDDR {};", state),
            Command::EndIR(state) => write!(f, "ENDIR {};", state),
            Command::Frequency(Some(freq)) => write!(f, "FREQUENCY {:E} HZ;", freq),
            Command::Frequency(None)       => write!(f, "FREQUENCY;"),
            Command::HDR(pattern) => write!(f, "HDR {};", pattern),
            Command::HIR(pattern) => write!(f, "HIR {};", pattern),
            Command::PIO(v) => {
                write!(f, "PIO (")?;
                for c in v.iter() {
                    c.fmt(f)?;
                }
                write!(f, ");\n")
            },
            Command::PIOMap(v) => {
                write!(f, "PIOMAP (\n")?;
                for (dir, name) in v.iter() {
                    write!(f, "    {} {}\n", dir, name)?;
                }
                write!(f, ");\n")
            },
            Command::RunTest { run_state, form, end_state } => {
                write!(f, "RUNTEST")?;
                if let Some(s) = run_state {
                    write!(f, " {}", s)?;
                }
                write!(f, " {}", form)?;
                if let Some(s) = end_state {
                    write!(f, " {}", s)?;
                }
                write!(f, ";")
            },
            Command::SDR(pattern) => write!(f, "SDR {};", pattern),
            Command::SIR(pattern) => write!(f, "SIR {};", pattern),
            Command::State { path, end } => {
                write!(f, "STATE")?;
                if let Some(path) = path {
                    for state in path.iter() {
                        write!(f, " {}", state)?;
                    }
                }
                write!(f, " {};", end)
            },
            Command::TDR(pattern) => write!(f, "TDR {};", pattern),
            Command::TIR(pattern) => write!(f, "TIR {};", pattern),
            Command::TRST(mode) => write!(f, "TRST {};", mode),
        }
    }
}

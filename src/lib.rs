// Copyright 2021 Adam Greig
// Licensed under the MIT license.

#![allow(clippy::upper_case_acronyms)]

//! # svf
//!
//! Parse and generate SVF files.
//!
//! Use [`parse_complete`] to parse a full SVF file into a vector of [`Command`],
//! or [`parse_iter`] to create an iterator over [`Command`] which parses incrementally.
//!
//! Once parsed, or if you construct [`Command`] manually, the Display trait
//! implementation can be used to generate SVF files.

mod display;
mod parser;
pub use parser::{parse_complete, parse_iter, SVFParseError as ParseError};

/// IEEE 1149.1 TAP states with SVF TAP state names.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum State {
    /// Test-Logic-Reset
    RESET,

    /// Run-Test/Idle
    IDLE,

    /// Select-DR-Scan
    DRSELECT,

    /// Capture-DR
    DRCAPTURE,

    /// Shift-DR
    DRSHIFT,

    /// Exit1-DR
    DREXIT1,

    /// Pause-DR
    DRPAUSE,

    /// Exit2-DR
    DREXIT2,

    /// Update-DR
    DRUPDATE,

    /// Select-IR-Scan
    IRSELECT,

    /// Capture-IR
    IRCAPTURE,

    /// Shift-IR
    IRSHIFT,

    /// Exit1-IR
    IREXIT1,

    /// Pause-IR
    IRPAUSE,

    /// Exit2-IR
    IREXIT2,

    /// Update-IR
    IRUPDATE,
}

impl State {
    /// Check if this state is one of the stable states IRPAUSE, DRPAUSE, RESET, or IDLE.
    pub fn is_stable(&self) -> bool {
        matches!(self, State::DRPAUSE | State::IRPAUSE | State::RESET | State::IDLE)
    }

    /// Return the default path to move from the current state `self` to an end state `end`,
    /// when both `self` and `end` are stable states.
    ///
    /// The returned path only includes the intermediate states and not the start or end state.
    /// If either `self` or `end` are not stable, None is returned.
    pub fn default_path(&self, end: &State) -> Option<Vec<State>> {
        use State::*;
        match (self, end) {
            (RESET, RESET)      => Some(vec![]),
            (RESET, IDLE)       => Some(vec![]),
            (RESET, DRPAUSE)    => Some(vec![IDLE, DRSELECT, DRCAPTURE, DREXIT1]),
            (RESET, IRPAUSE)    => Some(vec![IDLE, DRSELECT, IRSELECT, IRCAPTURE, IREXIT1]),
            (IDLE, RESET)       => Some(vec![DRSELECT, IRSELECT]),
            (IDLE, IDLE)        => Some(vec![]),
            (IDLE, DRPAUSE)     => Some(vec![DRSELECT, DRCAPTURE, DREXIT1]),
            (IDLE, IRPAUSE)     => Some(vec![DRSELECT, IRSELECT, IRCAPTURE, IREXIT1]),
            (DRPAUSE, RESET)    => Some(vec![DREXIT2, DRUPDATE, DRSELECT, IRSELECT]),
            (DRPAUSE, IDLE)     => Some(vec![DREXIT2, DRUPDATE]),
            (DRPAUSE, DRPAUSE)  => Some(vec![DREXIT2, DRUPDATE, DRSELECT, DRCAPTURE, DREXIT1]),
            (DRPAUSE, IRPAUSE)  => Some(vec![DREXIT2, DRUPDATE, DRSELECT, IRSELECT, IRCAPTURE,
                                             IREXIT1]),
            (IRPAUSE, RESET)    => Some(vec![IREXIT2, IRUPDATE, DRSELECT, IRSELECT]),
            (IRPAUSE, IDLE)     => Some(vec![IREXIT2, IRUPDATE]),
            (IRPAUSE, DRPAUSE)  => Some(vec![IREXIT2, IRUPDATE, DRSELECT, DRCAPTURE, DREXIT1]),
            (IRPAUSE, IRPAUSE)  => Some(vec![IREXIT2, IRUPDATE, DRSELECT, IRSELECT, IRCAPTURE,
                                             IREXIT1]),
            _                   => None,
        }
    }
}

/// Vector characters for a parallel test vector.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum VectorChar {
    /// Drive logical 1
    H,

    /// Drive logical 0
    L,

    /// Drive high impedance
    Z,

    /// Detect logical 1
    U,

    /// Detect logical 0
    D,

    /// Detect unknown
    X,
}

/// Data pattern used for HDR, HIR, SDR, SIR, TDR, and TIR commands.
#[derive(Clone, Debug, PartialEq)]
pub struct Pattern {
    /// Number of bits to be scanned.
    pub length: u32,

    /// Value to be scanned into the target.
    /// If not specified, the previously specified TDI for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first,
    /// and the vector is automatically zero-padded to contain enough bits for the length.
    pub tdi: Option<Vec<u8>>,

    /// Value to compare against actual values scanned out of the target.
    /// If not specified, no comparison is performed.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first,
    /// and the vector is automatically zero-padded to contain enough bits for the length.
    pub tdo: Option<Vec<u8>>,

    /// Mask used when comparing TDO values against actual values.
    /// 1 indicates care, 0 indicates don't-care.
    /// If not specified, the previously specified MASK for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first,
    /// and the vector is automatically zero-padded to contain enough bits for the length.
    pub mask: Option<Vec<u8>>,

    /// Mask TDI data.
    /// 1 indicates care, 0 indicates don't-care.
    /// If not specified, the previously specified SMASK for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first,
    /// and the vector is automatically zero-padded to contain enough bits for the length.
    pub smask: Option<Vec<u8>>,
}

impl Pattern {
    /// Extend all non-None scan data to contain as many trailing 0s
    /// as required to make up the bit length.
    fn extend(mut self) -> Self {
        for data in [&mut self.tdi, &mut self.tdo, &mut self.mask, &mut self.smask].iter_mut() {
            if let Some(data) = data {
                while data.len() * 8 < self.length as usize {
                    data.push(0);
                }
            }
        }
        self
    }
}

/// Possible directions for a column in a PIOMAP command.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum PIOMapDirection {
    /// Input to the unit under test, uses H, L, or Z characters.
    In,

    /// Output from the unit under test, uses U, D, or X characters.
    Out,

    /// Bidirectional, may use any characters.
    InOut,
}

/// Possible clocks for the `run_clk` argument to RUNTEST.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RunClock {
    /// Test clock
    TCK,

    /// System clock
    SCK,
}

/// Possible modes for the TRST signal.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TRSTMode {
    /// Active (logic 0)
    On,

    /// Active (logic 1)
    Off,

    /// High impedance
    Z,

    /// Not present
    Absent,
}

/// Minimum and optional maximum time to run a RunTest command for.
#[derive(Clone, Debug, PartialEq)]
pub struct RunTestTime {
    pub min: f64,
    pub max: Option<f64>,
}

/// Possible forms of the RunTest arguments.
#[derive(Clone, Debug, PartialEq)]
pub enum RunTestForm {
    Clocked {
        run_count: u32,
        run_clk: RunClock,
        time: Option<RunTestTime>,
    },
    Timed(RunTestTime),
}

/// SVF command and corresponding parsed data.
#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    /// State for the bus after a DR scan.
    ///
    /// The state is checked to be a stable state when parsing.
    EndDR(State),

    /// State for the bus after an IR scan.
    ///
    /// The state is checked to be a stable state when parsing.
    EndIR(State),

    /// Maximum TCK frequency for subsequent scans, state changes, and test operations.
    Frequency(Option<f64>),

    /// Default header pattern to be shifted in before every data register scan operation.
    HDR(Pattern),

    /// Default header pattern to be shifted in before every instruction register scan operation.
    HIR(Pattern),

    /// Parallel input/output test vector.
    PIO(Vec<VectorChar>),

    /// Define I/O direction and name for each column in a PIO command.
    /// Each entry corresponds to a column with associated direction and logical name.
    PIOMap(Vec<(PIOMapDirection, String)>),

    /// Force the target to the specified state for a specified number of clocks
    /// or a specified length of time or both, then move to the specified end state.
    RunTest {
        /// State to hold during this command.
        /// Checked to be a stable state when parsing.
        /// If not specified, use the run_state specified in the previous RUNTEST command.
        run_state: Option<State>,

        /// The run_count, run_clk, min_time, and max_time parameters are stored
        /// in this RunTestForm enum which encodes the various ways in which they
        /// may be specified or omitted.
        form: RunTestForm,

        /// State to enter after completion of command.
        /// Checked to be a stable state when parsing.
        /// If not specified, use the default end state, which is the most
        /// recently specified end_state or run_state, or IDLE otherwise.
        end_state: Option<State>,
    },

    /// Scan data register with specified pattern.
    SDR(Pattern),

    /// Scan instruction register with specified pattern.
    SIR(Pattern),

    /// Force target to a stable state, optionally specifying the path to traverse.
    /// If no path is specified, use the default path between the current and final state.
    State {
        /// Path to take to reach the end state. States must be in an order that obeys the
        /// TAP state machine. If not specified, the default path from the current state to
        /// the end state is used.
        path: Option<Vec<State>>,

        /// Final state to reach. Checked to be a stable state when parsing.
        end: State,
    },

    /// Default trailer pattern to be shifted in before every data register scan operation.
    TDR(Pattern),

    /// Default trailer pattern to be shifted in before every instruction register scan operation.
    TIR(Pattern),

    /// Operation of TRST signal.
    TRST(TRSTMode),
}

// Copyright 2021 Adam Greig
// Licensed under the MIT license.

//! # svf
//!
//! Parse SVF files.

/// IEEE 1149.1 TAP states with SVF TAP state names.
#[derive(Copy, Clone, Debug)]
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
    DREXTI1,

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

/// Vector characters for a parallel test vector.
#[derive(Copy, Clone, Debug)]
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
#[derive(Clone, Debug)]
pub struct Pattern {
    /// Number of bits to be scanned.
    length: u32,

    /// Value to be scanned into the target.
    /// If not specified, the previously specified TDI for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first.
    tdi: Option<Vec<u8>>,

    /// Value to compare against actual values scanned out of the target.
    /// If not specified, no comparison is performed.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first.
    tdo: Option<Vec<u8>>,

    /// Mask used when comparing TDO values against actual values.
    /// 1 indicates care, 0 indicates don't-care.
    /// If not specified, the previously specified MASK for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first.
    mask: Option<Vec<u8>>,

    /// Mask TDI data.
    /// 1 indicates care, 0 indicates don't-care.
    /// If not specified, the previously specified SMASK for this command is used.
    /// Bits are packed into bytes least-significant-bit and least-significant-byte first.
    smask: Option<Vec<u8>>,
}

/// Possible directions for a column in a PIOMAP command.
#[derive(Copy, Clone, Debug)]
pub enum PIOMapDirection {
    /// Input to the unit under test, uses H, L, or Z characters.
    In,

    /// Output from the unit under test, uses U, D, or X characters.
    Out,

    /// Bidirectional, may use any characters.
    InOut,
}

/// Possible clocks for the `run_clk` argument to RUNTEST.
#[derive(Copy, Clone, Debug)]
pub enum RunClock {
    /// Test clock
    TCK,

    /// System clock
    SCK,
}

/// Possible modes for the TRST signal.
#[derive(Copy, Clone, Debug)]
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

/// SVF command and corresponding parsed data.
#[derive(Clone, Debug)]
pub enum Command {
    /// State for the bus after a DR scan.
    EndDR(State),

    /// State for the bus after an IR scan.
    EndIR(State),

    /// Maximum TCK frequency for subsequent scans, state changes, and test operations.
    Frequency(f32),

    /// Default header pattern shifted in before every data register scan operation.
    HDR(Pattern),

    /// Default header pattern shifted in before every instruction register scan operation.
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
        /// One of IRPAUSE, DRPAUSE, RESET, or IDLE.
        /// If not specified, uses the run_state specified in the previous RUNTEST command.
        run_state: Option<State>,

        /// Number of clocks to remain in the run state.
        run_count: Option<u32>,

        /// Clock used to count cycles, either TCK or SCK.
        run_clk: Option<RunClock>,

        /// Minimum amount of time in seconds to stay in run_state.
        min_time: Option<f32>,

        /// Maximum amount of time in seconds to stay in run_state.
        max_time: Option<f32>,

        /// State to enter after completion of command.
        /// One of IRPAUSE, DRPAUSE, RESET, or IDLE.
        /// If not specified, the default end state is used, which is the most
        /// recently specified end_state or run_state, or IDLE.
        end_state: Option<State>,
    },

    /// Scan data register with specified pattern.
    SDR(Pattern),

    /// Scan instruction register with specified pattern.
    SIR(Pattern),

    /// Force target to a stable state, optionally specifying the path to traverse.
    /// If no path is specified, the default path for the current and final state is used.
    State {
        /// Path to take to reach the end state. States must be in an order that obeys the
        /// TAP state machine. If not specified, the default path from the current state to
        /// the end state is used.
        /// Valid states are RESET, IDLE, DRSELECT, DRCAPTURE, DRSHIFT, DRPAUSE, DREXIT1,
        /// DREXIT2, DRUPDATE, IRSELECT, IRCAPTURE, IRSHIFT, IRPAUSE, IREXIT1, IREXIT2, and
        /// IRUPDATE.
        path: Option<Vec<State>>,

        /// Final state to reach. Must be one of IRPAUSE, DRPAUSE, RESET, or IDLE.
        end: State,
    },

    /// Default trailer pattern shifted in before every data register scan operation.
    TDR(Pattern),

    /// Default trailer pattern shifted in before every instruction register scan operation.
    TIR(Pattern),

    /// Operation of TRST signal.
    TRST(TRSTMode),
}

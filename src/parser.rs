use thiserror::Error;
use nom::{
    branch::{alt, permutation},
    bytes::streaming::{tag, tag_no_case, is_a},
    combinator::{complete, all_consuming, opt, recognize, success, map, map_res, cut},
    character::streaming::{
        char as nom_char, hex_digit1, line_ending, not_line_ending, digit1, multispace1, alpha1,
    },
    character::complete::multispace1 as multispace1_complete,
    multi::{many0, many1, many0_count, many1_count, separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
    error::{ErrorKind, ParseError, FromExternalError},
};
use nom_locate::LocatedSpan;

use super::{
    Command,
    PIOMapDirection,
    Pattern,
    RunClock,
    RunTestForm,
    RunTestTime,
    State,
    TRSTMode,
    VectorChar,
};

// Alias Span for brevity.
type Span<'a> = LocatedSpan<&'a str>;

/// Location of a parsing error in the SVF file.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ErrLoc {
    /// Line number where parsing error occurred.
    line: usize,
    /// Column number where parsing error occurred.
    col: usize,
}

impl<'a> std::convert::From<Span<'a>> for ErrLoc {
    fn from(span: Span<'a>) -> Self {
        ErrLoc { line: span.location_line() as usize, col: span.get_column() }
    }
}

impl std::fmt::Display for ErrLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "L{}:{}", self.line, self.col)
    }
}

/// SVF parse error.
///
/// Each error contains the input that caused the error and
/// potentially other relevant metadata.
#[derive(Clone, Debug, PartialEq, Error)]
pub enum SVFParseError {
    #[error("Could not parse f64 from real number at {0}")]
    InvalidF64(ErrLoc),
    #[error("Could not parse u32 from decimal number at {0}")]
    InvalidU32(ErrLoc),
    #[error("Invalid PIO map indices specified at {0}")]
    BadPIOMapIndices(ErrLoc),
    #[error("State '{1:?}' is not a stable state at {0}")]
    NotStableState(ErrLoc, State),
    #[error("RunTest command has invalid arguments at {0}")]
    InvalidRunTest(ErrLoc),
    #[error("Incomplete data at {0}: retry with at least {1} more bytes of data")]
    Incomplete(ErrLoc, usize),
    #[error("Parser error type {1:?} at {0}")]
    Parser(ErrLoc, String),
}

impl<'a> ParseError<Span<'a>> for SVFParseError {
    fn from_error_kind(input: Span<'a>, kind: ErrorKind) -> Self {
        SVFParseError::Parser(input.into(), kind.description().to_string())
    }
    fn append(_: Span<'a>, _: ErrorKind, other: Self) -> Self {
        other
    }
}

impl<'a> From<(Span<'a>, ErrorKind)> for SVFParseError {
    fn from((i, kind): (Span<'a>, ErrorKind)) -> Self {
        SVFParseError::Parser(i.into(), kind.description().to_string())
    }
}

impl<I: std::fmt::Debug> FromExternalError<I, SVFParseError> for SVFParseError {
    fn from_external_error(_: I, _: ErrorKind, e: SVFParseError) -> Self {
        e
    }
}

/// Type alias IResult to use SVFParseError by default.
type IResult<I, O, E = SVFParseError> = Result<(I, O), nom::Err<E>>;

/// Parse a comment, which starts with `//` or `!` and finishes at an end-of-line.
///
/// Returns the string contents of the comment.
fn comment(input: Span) -> IResult<Span, Span> {
    delimited(alt((tag("//"), tag("!"))),
              not_line_ending,
              line_ending,
    )(input)
}

/// Consume any amount of comments or whitespace.
fn ws0(input: Span) -> IResult<Span, Span> {
    recognize(many0_count(alt((comment, multispace1))))(input)
}

/// Consume any amount of whitespace where the input is known to be complete.
///
/// This method will consume all whitespace to the end of the input,
/// but not then return Incomplete suggesting more could potentially be read.
fn ws0_complete(input: Span) -> IResult<Span, Span> {
    recognize(many0_count(complete(alt((comment, multispace1_complete)))))(input)
}

/// Consume at least some comments or whitespace.
fn ws1(input: Span) -> IResult<Span, Span> {
    recognize(many1_count(alt((comment, multispace1))))(input)
}

/// Parse scan data, which is always hexadecimal data surrounded by brackets.
///
/// Any comments or whitespace inside the brackets are ignored.
///
/// Returns the parsed data as a `Vec<u8>`, least significant byte first,
/// with any leading 0s stripped out.
fn scandata(input: Span) -> IResult<Span, Vec<u8>> {
    let (i, hex) = delimited(
        nom_char('('),
        many1(delimited(ws0, hex_digit1, ws0)),
        nom_char(')')
    )(input)?;
    let chars: String = hex.iter().map(|h| *h.fragment()).collect();
    let chars: Vec<char> = chars.trim_start_matches('0').chars().collect();
    let data = chars.rchunks(2).map(|nibbles| {
        let word = nibbles.iter().collect::<String>();
        u8::from_str_radix(&word, 16).expect("Internal error parsing hexadecimal number")
    }).collect();

    Ok((i, data))
}

/// Parse a vector string, consisting of zero or more of the letters H L Z U D X inside brackets.
///
/// Any comments or whitespace inside the brackets are ignored.
///
/// Returns the parsed data as a `Vec<VectorChar>`.
fn vector_string(input: Span) -> IResult<Span, Vec<VectorChar>> {
    map(
        delimited(
            nom_char('('),
            many0(alt((
                delimited(ws0, nom_char('H'), ws0),
                delimited(ws0, nom_char('L'), ws0),
                delimited(ws0, nom_char('Z'), ws0),
                delimited(ws0, nom_char('U'), ws0),
                delimited(ws0, nom_char('D'), ws0),
                delimited(ws0, nom_char('X'), ws0),
            ))),
            nom_char(')')
        ),
        |chars| chars.iter().map(|c| match c {
            'H' => VectorChar::H,
            'L' => VectorChar::L,
            'Z' => VectorChar::Z,
            'U' => VectorChar::U,
            'D' => VectorChar::D,
            'X' => VectorChar::X,
            _   => unreachable!(),
        }).collect()
    )(input)
}

fn logical_name(input: Span) -> IResult<Span, Span> {
    recognize(preceded(alpha1, many0(alt((alpha1, digit1, is_a("_"))))))(input)
}

/// Parse the direction form of PIOMAP column descriptions, where each column
/// is listed in order and given a direction and name.
fn piomap_dir(input: Span) -> IResult<Span, Vec<(PIOMapDirection, String)>> {
    map(
        delimited(
            nom_char('('),
            delimited(
                ws0,
                separated_list0(
                    ws1,
                    tuple((
                        alt((tag_no_case("INOUT"), tag_no_case("IN"), tag_no_case("OUT"))),
                        preceded(ws1, logical_name),
                    ))
                ),
                ws0,
            ),
            nom_char(')'),
        ),
        |v| v.iter().map(|(dirn, name)| match *dirn.fragment() {
            "IN"    => (PIOMapDirection::In, name.to_string()),
            "OUT"   => (PIOMapDirection::Out, name.to_string()),
            "INOUT" => (PIOMapDirection::InOut, name.to_string()),
            _       => unreachable!(),
        }).collect()
    )(input)
}

/// Parse the indexed form of PIOMAP column descriptions, where each column is given
/// its column number and a name, and the direction is implicitly INOUT.
///
/// Returns the same `Vec<(PIOMapDirection, String)>` as `piomap_dir`; the indices
/// are used to order the vector of names and missing signals are filled in.
fn piomap_idx(input: Span) -> IResult<Span, Vec<(PIOMapDirection, String)>> {
    // First parse the input to a vec of the specified (u32, String).
    let (i, mut v): (Span, Vec<(u32, String)>) = map(
        delimited(
            nom_char('('),
            delimited(
                ws0,
                separated_list0(
                    ws1,
                    tuple((
                        decimal,
                        preceded(ws1, logical_name),
                    ))
                ),
                ws0,
            ),
            nom_char(')'),
        ),
        |v| v.iter().map(|(idx, name)| (*idx, name.to_string())).collect()
    )(input)?;

    // Return early if no elements were specified.
    if v.is_empty() {
        return Ok((i, vec![]))
    }

    // Check no indices are missing and none are 0.
    v.sort_unstable_by_key(|(idx, _)| *idx);
    for (iter_idx, (col_idx, _)) in v.iter().enumerate() {
        if *col_idx as usize != iter_idx + 1 {
            return Err(nom::Err::Failure(SVFParseError::BadPIOMapIndices(input.into())));
        }
    }

    // Convert to output type.
    let v = v.iter().map(|(_, name)| (PIOMapDirection::InOut, name.clone())).collect();

    Ok((i, v))
}

/// Parse a real number, which has the form `digits [ . digits ] [ E [ + | - ] digits ]`,
/// where `digits` is one or more of the characters 0-9.
///
/// Returns the parsed real number as an f64.
fn real(input: Span) -> IResult<Span, f64> {
    map_res(
        recognize(
            tuple((
                digit1,
                opt(preceded(nom_char('.'), digit1)),
                opt(preceded(
                    alt((nom_char('E'), nom_char('e'))),
                    tuple((opt(alt((nom_char('+'), nom_char('-')))), digit1))
                )),
            ))
        ),
        |float_str: Span| match float_str.parse::<f64>() {
            Ok(f) if f.is_finite() => Ok(f),
            _ => Err(SVFParseError::InvalidF64(input.into())),
        }
    )(input)
}

/// Parse an unsigned 32-bit decimal integer.
fn decimal(input: Span) -> IResult<Span, u32> {
    map_res(
        digit1,
        |decimal_str: Span| decimal_str.parse::<u32>()
                                       .map_err(|_| SVFParseError::InvalidU32(input.into()))
    )(input)
}

/// Parse one of the states.
///
/// Parsing is case insensitive. The corresponding State variant is returned.
fn state(input: Span) -> IResult<Span, State> {
    map(
        alt((
            tag_no_case("RESET"),
            tag_no_case("IDLE"),
            tag_no_case("DRSELECT"),
            tag_no_case("DRCAPTURE"),
            tag_no_case("DRSHIFT"),
            tag_no_case("DREXIT1"),
            tag_no_case("DRPAUSE"),
            tag_no_case("DREXIT2"),
            tag_no_case("DRUPDATE"),
            tag_no_case("IRSELECT"),
            tag_no_case("IRCAPTURE"),
            tag_no_case("IRSHIFT"),
            tag_no_case("IREXIT1"),
            tag_no_case("IRPAUSE"),
            tag_no_case("IREXIT2"),
            tag_no_case("IRUPDATE"),
        )),
        |s: Span| match s.to_ascii_uppercase().as_str() {
            "RESET"     => State::RESET,
            "IDLE"      => State::IDLE,
            "DRSELECT"  => State::DRSELECT,
            "DRCAPTURE" => State::DRCAPTURE,
            "DRSHIFT"   => State::DRSHIFT,
            "DREXIT1"   => State::DREXIT1,
            "DRPAUSE"   => State::DRPAUSE,
            "DREXIT2"   => State::DREXIT2,
            "DRUPDATE"  => State::DRUPDATE,
            "IRSELECT"  => State::IRSELECT,
            "IRCAPTURE" => State::IRCAPTURE,
            "IRSHIFT"   => State::IRSHIFT,
            "IREXIT1"   => State::IREXIT1,
            "IRPAUSE"   => State::IRPAUSE,
            "IREXIT2"   => State::IREXIT2,
            "IRUPDATE"  => State::IRUPDATE,
            _           => unreachable!(),
        }
    )(input)
}

/// Parse a run_clk option, either TCK or SCK.
fn run_clk(input: Span) -> IResult<Span, RunClock> {
    map(
        alt((tag_no_case("TCK"), tag_no_case("SCK"))),
        |s: Span| match s.to_ascii_uppercase().as_str() {
            "TCK" => RunClock::TCK,
            "SCK" => RunClock::SCK,
            _     => unreachable!(),
        }
    )(input)
}

/// Parse scandata preceded by a specific name, ignoring any whitespace between the
/// name and the scandata.
///
/// Returns the parsed scandata.
fn named_scandata<'a>(tag: &'static str)
    -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<u8>>
{
    preceded(
        terminated(
            tag_no_case(tag),
            ws0,
        ),
        scandata,
    )
}

/// Parse a Pattern, consisting of a length and optionally any of
/// TDI, TDO, MASK, or SMASK data.
///
/// The pattern starts with the length integer.
///
/// Returns a Pattern struct.
fn pattern(input: Span) -> IResult<Span, Pattern> {

    /// Maps _ to a parser that always returns None, and maps literals
    /// to a delimited named_scandata with that tag, mapped to return Some(Vec<u8>).
    macro_rules! pattern_tag {
        (_) => {
            success(None)
        };
        ($tag:literal) => {
            map(preceded(ws0, named_scandata($tag)), |x| Some(x))
        };
    }

    /// Emits a permutation over the provided inputs, which may be either
    /// a _ to return always None or a tag to return a named_scandata of that tag.
    macro_rules! pattern_data {
        ($($tag:tt),+) => {
            permutation(($( pattern_tag!($tag)),*))
        };
    }

    map(
        tuple((
            // Match the mandatory length field.
            decimal,
            // Unfortunately permutation() does not support optional inputs;
            // if each sub-parser was wrapped in opt() then they'd all succeed
            // immediately, most with None. Instead, we use permutation to
            // allow any ordering of mandatory arguments, and then use alt
            // to provide all possible combinations of provided arguments.
            // To ensure the return type of each permutation matches, the
            // missing arguments are replaced with a success(None) parser.
            // The options are listed in descending order of number of arguments,
            // to ensure the versions with fewer arguments cannot match first.
            alt((
                pattern_data!("TDI", "TDO", "MASK", "SMASK"),

                pattern_data!("TDI", "TDO", "MASK",       _),
                pattern_data!("TDI", "TDO",      _, "SMASK"),
                pattern_data!("TDI",     _, "MASK", "SMASK"),
                pattern_data!(    _, "TDO", "MASK", "SMASK"),

                pattern_data!("TDI", "TDO",      _,       _),
                pattern_data!("TDI",     _, "MASK",       _),
                pattern_data!("TDI",     _,      _, "SMASK"),
                pattern_data!(    _, "TDO", "MASK",       _),
                pattern_data!(    _, "TDO",      _, "SMASK"),
                pattern_data!(    _,     _, "MASK", "SMASK"),

                pattern_data!("TDI",     _,      _,       _),
                pattern_data!(    _, "TDO",      _,       _),
                pattern_data!(    _,     _, "MASK",       _),
                pattern_data!(    _,     _,      _, "SMASK"),

                pattern_data!(    _,     _,      _,       _),
            )),
        )),
        |pattern| Pattern {
            length: pattern.0,
            tdi: pattern.1.0,
            tdo: pattern.1.1,
            mask: pattern.1.2,
            smask: pattern.1.3,
        }.extend()
    )(input)
}

/// Parse the ENDDR and ENDIR commands, which specify a stable state.
fn command_enddr_endir(input: Span) -> IResult<Span, Command> {
    map_res(
        tuple((
            terminated(alt((tag_no_case("ENDDR"), tag_no_case("ENDIR"))), ws1),
            cut(terminated(
                delimited(ws0, state, ws0),
                nom_char(';'),
            )),
        )),
        |(c, s)| if !s.is_stable() {
            Err(SVFParseError::NotStableState(input.into(), s))
        } else {
            match c.to_ascii_uppercase().as_str() {
                "ENDDR" => Ok(Command::EndDR(s)),
                "ENDIR" => Ok(Command::EndIR(s)),
                _       => unreachable!(),
            }
        }
    )(input)
}

/// Parse the FREQUENCY command, which specifies a real number frequency.
fn command_frequency(input: Span) -> IResult<Span, Command> {
    map(delimited(
        tag_no_case("FREQUENCY"),
        cut(opt(delimited(ws1, cut(real), preceded(ws0, tag_no_case("HZ"))))),
        cut(preceded(ws0, nom_char(';'))),
    ), |f| Command::Frequency(f))(input)
}

/// Parse the HDR, HIR, TDR, TIR, SDR, and SIR commands, which all specify patterns.
fn command_hdr_hir_tdr_tir_sdr_sir(input: Span) -> IResult<Span, Command> {
    map(
        tuple((
            terminated(alt((
                tag_no_case("HDR"),
                tag_no_case("HIR"),
                tag_no_case("TDR"),
                tag_no_case("TIR"),
                tag_no_case("SDR"),
                tag_no_case("SIR"),
            )), ws1),
            cut(terminated(
                delimited(ws0, pattern, ws0),
                nom_char(';'),
            )),
        )),
        |(c, p)| match c.to_ascii_uppercase().as_str() {
            "HDR" => Command::HDR(p),
            "HIR" => Command::HIR(p),
            "TDR" => Command::TDR(p),
            "TIR" => Command::TIR(p),
            "SDR" => Command::SDR(p),
            "SIR" => Command::SIR(p),
            _     => unreachable!(),
        }
    )(input)
}

/// Parse the PIO command, which specifies a vector string.
fn command_pio(input: Span) -> IResult<Span, Command> {
    map(delimited(
        terminated(tag_no_case("PIO"), ws1),
        cut(delimited(ws0, vector_string, ws0)),
        cut(nom_char(';')),
    ), |vs| Command::PIO(vs))(input)
}

/// Parse the PIOMAP command, which specifies column names and directions for PIO.
fn command_piomap(input: Span) -> IResult<Span, Command> {
    map(
        delimited(
            terminated(tag_no_case("PIOMAP"), ws1),
            cut(delimited(ws0, alt((piomap_dir, piomap_idx)), ws0)),
            cut(nom_char(';')),
        ),
        |v| Command::PIOMap(v),
    )(input)
}

/// Parse the RUNTEST command.
fn command_runtest(input: Span) -> IResult<Span, Command> {
    map_res(
        delimited(
            terminated(tag_no_case("RUNTEST"), ws1),
            // Match either form of command:
            // 1) [run_state] run_count run_clk [min_time [max_time]] [end_state]
            // 2) [run_state] None      None     min_time [max_time]  [end_state]
            cut(alt((
                tuple((
                    opt(terminated(state, ws1)),
                    map(tuple((
                        terminated(decimal, ws1),
                        run_clk,
                    )), |x| Some(x)),
                    opt(tuple((
                        delimited(ws1, real, preceded(ws1, tag_no_case("SEC"))),
                        opt(delimited(
                            delimited(ws1, tag_no_case("MAXIMUM"), ws1),
                            cut(real),
                            preceded(ws1, tag_no_case("SEC"))
                        )),
                    ))),
                    opt(preceded(delimited(ws1, tag_no_case("ENDSTATE"), ws1), state)),
                )),
                tuple((
                    opt(terminated(state, ws1)),
                    success(None),
                    map(tuple((
                        terminated(cut(real), preceded(ws1, tag_no_case("SEC"))),
                        opt(delimited(
                            delimited(ws1, tag_no_case("MAXIMUM"), ws1),
                            cut(real),
                            preceded(ws1, tag_no_case("SEC"))
                        )),
                    )), |x| Some(x)),
                    opt(preceded(delimited(ws1, tag_no_case("ENDSTATE"), ws1), state)),
                )),
            ))),
            cut(preceded(ws0, nom_char(';'))),
        ),
        |x| {
            // Check the run and end states, if specified, are stable states.
            if x.0.map(|x| x.is_stable()) == Some(false) {
                Err(SVFParseError::NotStableState(input.into(), x.0.unwrap()))
            } else if x.3.map(|x| x.is_stable()) == Some(false) {
                Err(SVFParseError::NotStableState(input.into(), x.3.unwrap()))
            } else {
                // Extract the optional min_time and max_time parameters.
                let time = x.2.map(|(min, max)| RunTestTime { min, max });
                // Determine the specified form of the command.
                let form = match x.1 {
                    // If run_count and run_clk are specified, use Clocked with an optional time.
                    Some((run_count, run_clk)) => RunTestForm::Clocked {
                        run_count, run_clk, time,
                    },
                    // If neither are specified, use time if available.
                    // If neither run_count nor run_clk are specified, use time if available,
                    // otherwise return an error.
                    None => match time {
                        Some(time) => RunTestForm::Timed(time),
                        None       => return Err(SVFParseError::InvalidRunTest(input.into())),
                    },
                };
                Ok(Command::RunTest {
                    run_state: x.0,
                    form,
                    end_state: x.3,
                })
            }
        }
    )(input)
}

/// Parse the STATE command, which specifies a new end state and optionally
/// the path to take to get there.
fn command_state(input: Span) -> IResult<Span, Command> {
    map_res(
        delimited(
            terminated(tag_no_case("STATE"), ws1),
            cut(terminated(separated_list1(ws1, state), ws0)),
            cut(nom_char(';')),
        ),
        |mut path| {
            let end = path.pop().expect("Internal error: no end state found");
            if !end.is_stable() {
                Err(SVFParseError::NotStableState(input.into(), end))
            } else if path.is_empty() {
                Ok(Command::State { path: None, end })
            } else {
                Ok(Command::State { path: Some(path), end })
            }
        }
    )(input)
}

/// Parse the TRST command, whicih specifies the operation of the optional TRST signal.
fn command_trst(input: Span) -> IResult<Span, Command> {
    map(
        delimited(
            terminated(tag_no_case("TRST"), ws1),
            cut(terminated(
                alt((
                    tag_no_case("ON"),
                    tag_no_case("OFF"),
                    tag_no_case("Z"),
                    tag_no_case("ABSENT"),
                )),
                ws0
            )),
            cut(nom_char(';')),
        ),
        |mode| match mode.to_ascii_uppercase().as_str() {
            "ON"     => Command::TRST(TRSTMode::On),
            "OFF"    => Command::TRST(TRSTMode::Off),
            "Z"      => Command::TRST(TRSTMode::Z),
            "ABSENT" => Command::TRST(TRSTMode::Absent),
            _        => unreachable!(),
        }
    )(input)
}

/// Parse any command.
fn command(input: Span) -> IResult<Span, Command> {
    alt((
        command_enddr_endir,
        command_frequency,
        command_hdr_hir_tdr_tir_sdr_sir,
        command_pio,
        command_piomap,
        command_runtest,
        command_state,
        command_trst,
    ))(input)
}

/// Parse complete input into a vector of commands.
///
/// Returns an error if the input could not be fully parsed.
pub fn parse(input: &str) -> Result<Vec<Command>, SVFParseError> {
    all_consuming(terminated(
        many0(complete(preceded(ws0, command))),
        ws0_complete,
    ))(Span::new(input))
        .map(|(_, commands)| commands)
        .map_err(|e| match e {
            nom::Err::Error(e)   => e,
            nom::Err::Failure(e) => e,
            _                    => unreachable!(),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Shorthand for creating a span.
    macro_rules! s {
        ($s:expr) => { Span::new($s) }
    }

    /// Assert that parsing the input $i with the parser $p
    /// produces the remaining output $r and possibly an output
    /// $o which may be a literal (compared to a span fragment)
    /// or any other expression (compared directly to parser otuput).
    macro_rules! assert_parse {
        // Literal output comparison.
        ($p:expr, $i:expr, $r:expr, $o:literal) => {
            match $p(Span::new($i)) {
                Ok((rem, out)) => {
                    assert_eq!(rem.fragment(), &$r);
                    assert_eq!(out.fragment(), &$o);
                }
                Err(e) => panic!("Parse failure: {:?}", e),
            }
        };

        // Other output type comparison.
        ($p:expr, $i:expr, $r:expr, $o:expr) => {
            match $p(Span::new($i)) {
                Ok((rem, out)) => {
                    assert_eq!(rem.fragment(), &$r);
                    assert_eq!(out, $o);
                }
                Err(e) => panic!("Parse failure: {:?}", e),
            }
        };

        // Output ignored, only check leftover input.
        ($p:expr, $i:expr, $r:expr) => {
            match $p(Span::new($i)) {
                Ok((rem, _)) => {
                    assert_eq!(rem.fragment(), &$r);
                }
                Err(e) => panic!("Parse failure: {:?}", e),
            }
        };
    }

    /// Assert that parsing the input $i with the parser $p fails,
    /// optionally checking the error against $e.
    macro_rules! assert_parse_err {
        ($p:expr, $i:literal) => {
            assert!($p(Span::new($i)).is_err());
        };
        ($p:expr, $i:literal, $e:expr) => {
            assert_eq!($p(Span::new($i)), Err($e));
        };
    }

    #[test]
    fn test_comment() {
        assert_parse!(comment, "// this is a comment\n", "", " this is a comment");
        assert_parse!(comment, "!also a comment\r\n", "", "also a comment");
        assert_parse!(comment, "//this!is//a!comment//too!\n", "", "this!is//a!comment//too!");
    }

    #[test]
    fn test_ws0() {
        assert_parse!(ws0, "  // comment\n   ! more comments\n\t\t\t_", "_");
    }

    #[test]
    fn test_ws0_complete() {
        assert_parse!(ws0_complete, "  // comment\n   ! more comments\n\t\t\t", "");
    }

    #[test]
    fn test_scandata() {
        // Test leading zeros are removed.
        assert_parse!(scandata, "(0)", "", vec![]);
        assert_parse!(scandata, "(0000)", "", vec![]);

        // Test some example hex data is parsed correctly.
        assert_parse!(scandata, "(0504030201)", "", vec![1, 2, 3, 4, 5]);

        // Test an odd number of nibbles is parsed correctly.
        assert_parse!(scandata, "(abcde)", "", vec![0xde, 0xbc, 0x0a]);

        // Test interior whitespace is ignored.
        assert_parse!(scandata, "(01 02\n    03)", "", vec![3, 2, 1]);

        // Test interior comments are ignored.
        assert_parse!(scandata, "(01 // comment\n  02 03)", "", vec![3, 2, 1]);

        // Test non-hex characters are rejected.
        assert_parse_err!(scandata, "(1234 x 5678)");
    }

    #[test]
    fn test_vector_string() {
        use VectorChar::*;
        assert_parse!(vector_string, "(HLUDXZHHLL)", "", vec![H, L, U, D, X, Z, H, H, L, L]);
        assert_parse!(vector_string, "( H\nL!c\nU\t    D)", "", vec![H, L, U, D]);
    }

    #[test]
    fn test_logical_name() {
        assert_parse!(logical_name, "A ", " ", "A");
        assert_parse!(logical_name, "Strobe ", " ", "Strobe");
        assert_parse!(logical_name, "STROBE_0 ", " ", "STROBE_0");
        assert_parse!(logical_name, "X_1_A ", " ", "X_1_A");
        assert_parse_err!(logical_name, "1A");
    }

    #[test]
    fn test_piomap_dir() {
        use PIOMapDirection::*;
        assert_parse!(piomap_dir, "( )", "", vec![]);
        assert_parse!(
            piomap_dir, "(IN A OUT B INOUT C)",
            "", vec![(In, "A".to_string()), (Out, "B".to_string()), (InOut, "C".to_string())]
        );
        assert_parse!(
            piomap_dir, "(  IN \n A OUT B // comment\n INOUT C    )",
            "", vec![(In, "A".to_string()), (Out, "B".to_string()), (InOut, "C".to_string())]
        );
    }

    #[test]
    fn test_piomap_idx() {
        use PIOMapDirection::*;
        assert_parse!(piomap_idx, "( )", "", vec![]);
        assert_parse!(
            piomap_idx, "(1 A 2 B)",
            "", vec![(InOut, "A".to_string()), (InOut, "B".to_string())]
        );
        assert_parse_err!(piomap_idx, "(0 A 1 B)");
        assert_parse_err!(piomap_idx, "(1 A 3 C)");
    }

    #[test]
    fn test_real() {
        // Test a variety of number formats parse correctly.
        // We terminate each string with a space to indicate to the streaming decoders that the whole
        // number has been received, since spaces are not permitted inside numbers.
        assert_parse!(real, "123 ", " ", (123.0));
        assert_parse!(real, "123.45 ", " ", (123.45));
        assert_parse!(real, "123e1 ", " ", (123e1));
        assert_parse!(real, "123E1 ", " ", (123e1));
        assert_parse!(real, "123e+10 ", " ", (123e10));
        assert_parse!(real, "123e-10 ", " ", (123e-10));
        assert_parse!(real, "123.45e11 ", " ", (123.45e11));
        assert_parse!(real, "123.45e-11 ", " ", (123.45e-11));

        // Test the strings the specification specifically lists as being valid .
        for n in &["1 ", "1E0 ", "1E+0 ", "1.0 ", "1.0E0 ", "1.0E+0 ", "1.0E-0 "] {
            assert_parse!(real, n, " ", (1.0));
        }

        // Test the strings the specification specifically lists as being invalid.
        for n in &["1. ", "1.E0 ", ".5 ", ".5E0 "] {
            // We want to either error, or only perform an incomplete parse,
            // with some remaining data that will later cause an error.
            let result = real(s!(n));
            assert!(result.is_err() || result.unwrap().0 != s!(" "));
        }
    }

    #[test]
    fn test_decimal() {
        assert_parse!(decimal, "12345 ", " ", (12345u32));
        assert_parse!(decimal, "00012 ", " ", (12));
        assert_parse_err!(decimal, "a1");
        assert_parse_err!(decimal, "-1");
        assert_parse_err!(decimal, "4294967296");
    }

    #[test]
    fn test_state() {
        assert_parse!(state, "DrExiT1", "", State::DREXIT1);
        assert_parse_err!(state, "notastate");
    }

    #[test]
    fn test_run_clk() {
        assert_parse!(run_clk, "TCK", "", RunClock::TCK);
        assert_parse!(run_clk, "sck", "", RunClock::SCK);
        assert_parse_err!(run_clk, "nck");
    }

    #[test]
    fn test_named_scandata() {
        // Test basic examples with spaces all work.
        assert_parse!(named_scandata("TDI"), "TDI (1)", "", vec![1]);
        assert_parse!(named_scandata("TDI"), "TDI \n (\n    1\n)", "", vec![1]);
        assert_parse!(named_scandata("TDO"), "TDO\t(\n1\n)", "", vec![1]);

        // Test error on mismatched tag.
        assert_parse_err!(named_scandata("TDI"), "TDO (1)");

        // Test error with non-space characters between tag and scandata.
        assert_parse_err!(named_scandata("TDI"), "TDI is (1)");
    }

    #[test]
    fn test_pattern() {
        // Test basic examples of patterns.
        // Each example is terminated with _ to make it clear no further
        // pattern input can be received.
        assert_parse!(
            pattern, "0_", "_", Pattern {
                length: 0,
                tdi: None,
                tdo: None,
                mask: None,
                smask: None,
            }
        );
        assert_parse!(
            pattern, "16 TDI (1)_", "_", Pattern {
                length: 16,
                tdi: Some(vec![1, 0]),
                tdo: None,
                mask: None,
                smask: None,
            }
        );
        assert_parse!(
            pattern, "8 MASK (3)_", "_", Pattern {
                length: 8,
                tdi: None,
                tdo: None,
                mask: Some(vec![3]),
                smask: None,
            }
        );
        assert_parse!(
            pattern, "3 TDI (1) TDO (2) MASK (3) SMASK (4)_", "_", Pattern {
                length: 3,
                tdi: Some(vec![1]),
                tdo: Some(vec![2]),
                mask: Some(vec![3]),
                smask: Some(vec![4]),
            }
        );
        assert_parse!(
            pattern, "3 SMASK (4) MASK (3) TDI (1) TDO (2)_", "_", Pattern {
                length: 3,
                tdi: Some(vec![1]),
                tdo: Some(vec![2]),
                mask: Some(vec![3]),
                smask: Some(vec![4]),
            }
        );
    }

    #[test]
    fn test_command_enddr_endir() {
        assert_parse!(command_enddr_endir, "ENDDR IDLE;", "", Command::EndDR(State::IDLE));
        assert_parse!(command_enddr_endir, "ENDDR DRPAUSE;", "", Command::EndDR(State::DRPAUSE));
        assert_parse!(command_enddr_endir, "ENDIR RESET;", "", Command::EndIR(State::RESET));
        assert_parse!(command_enddr_endir, "ENDDR \n RESET ;", "", Command::EndDR(State::RESET));
        assert_parse!(command_enddr_endir, "ENDDR !c\n RESET ;", "", Command::EndDR(State::RESET));
    }

    #[test]
    fn test_command_frequency() {
        assert_parse!(command_frequency, "FREQUENCY 90e3 Hz;", "", Command::Frequency(Some(90e3)));
        assert_parse!(command_frequency, "FREQUENCY 1E5 Hz;", "", Command::Frequency(Some(1e5)));
        assert_parse!(command_frequency, "FREQUENCY;", "", Command::Frequency(None));
        assert_parse!(command_frequency, "FREQUENCY 1000000Hz;", "", Command::Frequency(Some(1e6)));
    }

    #[test]
    fn test_pattern_commands() {
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HDR 32 TDI(00000010) TDO(81818181) MASK(FFFFFFFF) SMASK(0);",
            "",
            Command::HDR(Pattern {
               length: 32,
               tdi: Some(vec![0x10, 0x00, 0x00, 0x00]),
               tdo: Some(vec![0x81, 0x81, 0x81, 0x81]),
               mask: Some(vec![0xFF, 0xFF, 0xFF, 0xFF]),
               smask: Some(vec![0x00, 0x00, 0x00, 0x00]),
            })
        );
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HIR 16 TDI(ABCD);",
            "", Command::HIR(Pattern {
               length: 16,
               tdi: Some(vec![0xCD, 0xAB]),
               tdo: None,
               mask: None,
               smask: None,
            })
        );
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HDR 0;",
            "", Command::HDR(Pattern {
                length: 0, tdi: None, tdo: None, mask: None, smask: None
            })
        );
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HDR 8 TDI (1) TDO (2) MASK (3);",
            "", Command::HDR(Pattern {
                length: 8, tdi: Some(vec![1]), tdo: Some(vec![2]), mask: Some(vec![3]), smask: None
            })
        );
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HDR 8 TDO (2) MASK (3);",
            "", Command::HDR(Pattern {
                length: 8, tdi: None, tdo: Some(vec![2]), mask: Some(vec![3]), smask: None
            })
        );
        assert_parse!(
            command_hdr_hir_tdr_tir_sdr_sir,
            "HDR 8 TDO (2);",
            "", Command::HDR(Pattern {
                length: 8, tdi: None, tdo: Some(vec![2]), mask: None, smask: None
            })
        );
    }

    #[test]
    fn test_command_pio() {
        use VectorChar::*;
        assert_parse!(
            command_pio, "PIO (HLUDXZHHLL);",
            "", Command::PIO(vec![H, L, U, D, X, Z, H, H, L, L])
        );
    }

    #[test]
    fn test_command_piomap() {
        use PIOMapDirection::*;
        assert_parse!(
            command_piomap,
            "PIOMAP (IN  STROBE
                     IN  ALE
                     OUT DISABLE
                     OUT ENABLE
                     OUT CLEAR
                     IN  SET);",
            "", Command::PIOMap(vec![
                (In, "STROBE".to_string()),
                (In, "ALE".to_string()),
                (Out, "DISABLE".to_string()),
                (Out, "ENABLE".to_string()),
                (Out, "CLEAR".to_string()),
                (In, "SET".to_string()),
            ])
        );
    }

    #[test]
    fn test_command_runtest() {
        assert_parse!(
            command_runtest, "RUNTEST 1000 TCK ENDSTATE DRPAUSE;",
            "", Command::RunTest {
                run_state: None,
                form: RunTestForm::Clocked {
                    run_count: 1000,
                    run_clk: RunClock::TCK,
                    time: None,
                },
                end_state: Some(State::DRPAUSE),
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST 20 SCK;",
            "", Command::RunTest {
                run_state: None,
                form: RunTestForm::Clocked {
                    run_count: 20,
                    run_clk: RunClock::SCK,
                    time: None,
                },
                end_state: None,
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST 1000000 TCK 1 SEC;",
            "", Command::RunTest {
                run_state: None,
                form: RunTestForm::Clocked {
                    run_count: 1000000,
                    run_clk: RunClock::TCK,
                    time: Some(RunTestTime { min: 1.0, max: None }),
                },
                end_state: None,
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST 10.0E-3 SEC MAXIMUM 50.0E-3 SEC ENDSTATE IDLE;",
            "", Command::RunTest {
                run_state: None,
                form: RunTestForm::Timed(RunTestTime {
                    min: 10e-3,
                    max: Some(50e-3),
                }),
                end_state: Some(State::IDLE),
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST DRPAUSE 50E-3 SEC ENDSTATE IDLE;",
            "", Command::RunTest {
                run_state: Some(State::DRPAUSE),
                form: RunTestForm::Timed(RunTestTime {
                    min: 50e-3,
                    max: None,
                }),
                end_state: Some(State::IDLE),
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST 1 SEC;",
            "", Command::RunTest {
                run_state: None,
                form: RunTestForm::Timed(RunTestTime {
                    min: 1.0,
                    max: None,
                }),
                end_state: None,
            }
        );
        assert_parse!(
            command_runtest, "RUNTEST IDLE 1E-2 SEC;",
            "", Command::RunTest {
                run_state: Some(State::IDLE),
                form: RunTestForm::Timed(RunTestTime {
                    min: 1e-2,
                    max: None,
                }),
                end_state: None,
            }
        );
    }

    #[test]
    fn test_command_state() {
        use State::*;
        assert_parse!(
            command_state, "STATE IDLE;",
            "", Command::State { path: None, end: IDLE }
        );
        assert_parse!(
            command_state, "STATE DRPAUSE;",
            "", Command::State { path: None, end: DRPAUSE }
        );
        assert_parse!(
            command_state, "STATE DREXIT2 DRUPDATE DRSELECT IRSELECT IRCAPTURE IREXIT1 IRPAUSE;",
            "", Command::State{
                path: Some(vec![DREXIT2, DRUPDATE, DRSELECT, IRSELECT, IRCAPTURE, IREXIT1]),
                end: IRPAUSE
            }
        );
    }

    #[test]
    fn test_command_trst() {
        use TRSTMode::*;
        assert_parse!(command_trst, "TRST ON;", "", Command::TRST(On));
        assert_parse!(command_trst, "TRST off;", "", Command::TRST(Off));
        assert_parse!(command_trst, "TRST    z  ;", "", Command::TRST(Z));
        assert_parse!(command_trst, "TRST absent;", "", Command::TRST(Absent));
    }

    #[test]
    fn test_command() {
        assert_parse!(command, "TRST ON;", "", Command::TRST(TRSTMode::On));
        assert_parse!(command, "FREQUENCY;", "", Command::Frequency(None));
    }

    #[test]
    fn test_parse() {
        assert_eq!(
            parse("ENDDR IDLE; FREQUENCY; SDR 1 TDI (0);"),
            Ok(vec![
                Command::EndDR(State::IDLE),
                Command::Frequency(None),
                Command::SDR(Pattern {
                    length: 1,
                    tdi: Some(vec![0]),
                    tdo: None, mask: None, smask: None,
                }),
            ])
        );
        assert_eq!(parse(" ENDDR IDLE; //x\n\n"), Ok(vec![Command::EndDR(State::IDLE)]));
    }
}

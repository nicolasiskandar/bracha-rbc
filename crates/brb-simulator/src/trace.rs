use brb_core::ProcessId;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceEvent {
    pub tick: u64,

    pub from: ProcessId,

    pub to: Option<ProcessId>,

    pub kind: String,

    pub value_hex: String,

    pub outcome: String,
}

impl TraceEvent {
    pub fn new(
        tick: u64,
        from: ProcessId,
        to: Option<ProcessId>,
        kind: &str,
        value: &[u8],
        outcome: &str,
    ) -> Self {
        TraceEvent {
            tick,
            from,
            to,
            kind: kind.to_string(),
            value_hex: value.iter().map(|b| format!("{:02x}", b)).collect(),
            outcome: outcome.to_string(),
        }
    }
}

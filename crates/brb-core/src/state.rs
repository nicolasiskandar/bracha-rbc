use std::collections::{HashMap, HashSet};

use crate::message::{ProcessId, Value};

#[derive(Default, Clone, Debug)]
pub struct ProcessState {
    pub echo_sent: Option<Value>,

    pub ready_sent: Option<Value>,

    pub delivered: Option<Value>,

    pub echo_senders: HashMap<Value, HashSet<ProcessId>>,

    pub ready_senders: HashMap<Value, HashSet<ProcessId>>,
}

impl ProcessState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn echo_count(&self, value: &Value) -> usize {
        self.echo_senders.get(value).map_or(0, |s| s.len())
    }

    pub fn ready_count(&self, value: &Value) -> usize {
        self.ready_senders.get(value).map_or(0, |s| s.len())
    }

    pub fn record_echo(&mut self, sender: ProcessId, value: Value) -> bool {
        self.echo_senders.entry(value).or_default().insert(sender)
    }

    pub fn record_ready(&mut self, sender: ProcessId, value: Value) -> bool {
        self.ready_senders.entry(value).or_default().insert(sender)
    }
}

use brb_core::ProcessId;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub enum SchedulePolicy {
    Fifo,

    Random {
        seed: u64,
    },

    DelayAll {
        ticks: u64,
    },

    Partition {
        side_a: HashSet<ProcessId>,
        side_b: HashSet<ProcessId>,
    },
}

use brb_core::{InstanceId, Message, ProcessId, Value};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub enum ByzantineStrategy {
    Silent,

    EquivocateInit {
        v1: Value,
        v2: Value,
        targets_v1: HashSet<ProcessId>,
    },

    DuplicateMessages {
        message: Message,
        count: u32,
    },

    EquivocateReady {
        v1: Value,
        v2: Value,
        targets_v1: HashSet<ProcessId>,
    },

    EquivocateEcho {
        v1: Value,
        v2: Value,
        targets_v1: HashSet<ProcessId>,
    },

    Composite(Vec<ByzantineStrategy>),
}

pub struct ByzantineProcess {
    pub id: ProcessId,
    pub strategy: ByzantineStrategy,
}

impl ByzantineProcess {
    pub fn new(id: ProcessId, strategy: ByzantineStrategy) -> Self {
        ByzantineProcess { id, strategy }
    }

    pub fn generate_messages(
        &self,
        instance: &InstanceId,
        all_processes: &[ProcessId],
    ) -> Vec<(ProcessId, Message)> {
        self.gen(&self.strategy, instance, all_processes)
    }

    fn gen(
        &self,
        strategy: &ByzantineStrategy,
        instance: &InstanceId,
        all: &[ProcessId],
    ) -> Vec<(ProcessId, Message)> {
        let others: Vec<ProcessId> = all.iter().copied().filter(|&p| p != self.id).collect();
        match strategy {
            ByzantineStrategy::Silent => vec![],

            ByzantineStrategy::EquivocateInit { v1, v2, targets_v1 } => others
                .iter()
                .map(|&p| {
                    let value = if targets_v1.contains(&p) {
                        v1.clone()
                    } else {
                        v2.clone()
                    };
                    (
                        p,
                        Message::Init {
                            instance: instance.clone(),
                            value,
                        },
                    )
                })
                .collect(),

            ByzantineStrategy::DuplicateMessages { message, count } => others
                .iter()
                .flat_map(|&p| (0..*count).map(move |_| (p, message.clone())))
                .collect(),

            ByzantineStrategy::EquivocateReady { v1, v2, targets_v1 } => others
                .iter()
                .map(|&p| {
                    let value = if targets_v1.contains(&p) {
                        v1.clone()
                    } else {
                        v2.clone()
                    };
                    (
                        p,
                        Message::Ready {
                            instance: instance.clone(),
                            value,
                        },
                    )
                })
                .collect(),

            ByzantineStrategy::EquivocateEcho { v1, v2, targets_v1 } => others
                .iter()
                .map(|&p| {
                    let value = if targets_v1.contains(&p) {
                        v1.clone()
                    } else {
                        v2.clone()
                    };
                    (
                        p,
                        Message::Echo {
                            instance: instance.clone(),
                            value,
                        },
                    )
                })
                .collect(),

            ByzantineStrategy::Composite(strategies) => strategies
                .iter()
                .flat_map(|s| self.gen(s, instance, all))
                .collect(),
        }
    }
}

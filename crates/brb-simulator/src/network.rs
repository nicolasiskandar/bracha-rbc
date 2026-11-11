use std::collections::{HashMap, VecDeque};

use rand::rngs::StdRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;

use brb_core::{Action, BroadcastInstance, Config, InstanceId, Message, ProcessId, Value};

use crate::adversary::ByzantineProcess;
use crate::scheduler::SchedulePolicy;
use crate::trace::TraceEvent;

#[derive(Debug, Clone)]
pub struct Envelope {
    pub from: ProcessId,
    pub to: ProcessId,
    pub message: Message,
    pub deliver_at_tick: u64,
}

#[derive(Debug, Clone)]
pub struct DeliveryEvent {
    pub tick: u64,
    pub process: ProcessId,
    pub value: Value,
    pub instance: InstanceId,
}

pub struct SimNetwork {
    pub honest: HashMap<ProcessId, BroadcastInstance>,

    pub byzantine: Vec<ByzantineProcess>,

    pub all_process_ids: Vec<ProcessId>,

    pub pending: VecDeque<Envelope>,

    pub deliveries: Vec<DeliveryEvent>,

    pub trace: Vec<TraceEvent>,

    pub tick: u64,

    pub policy: SchedulePolicy,

    rng: StdRng,

    pub instance_id: InstanceId,
}

impl SimNetwork {
    pub fn new(
        honest_ids: Vec<ProcessId>,
        byzantine_ids: Vec<ProcessId>,
        broadcaster: ProcessId,
        config: Config,
        instance_id: InstanceId,
        policy: SchedulePolicy,
        byzantine_processes: Vec<ByzantineProcess>,
    ) -> Self {
        let seed = match &policy {
            SchedulePolicy::Random { seed } => *seed,
            _ => 0,
        };

        let honest: HashMap<ProcessId, BroadcastInstance> = honest_ids
            .iter()
            .map(|&id| {
                (
                    id,
                    BroadcastInstance::new(instance_id.clone(), id, broadcaster, config),
                )
            })
            .collect();

        let mut all_process_ids = honest_ids;
        all_process_ids.extend_from_slice(&byzantine_ids);

        SimNetwork {
            honest,
            byzantine: byzantine_processes,
            all_process_ids,
            pending: VecDeque::new(),
            deliveries: Vec::new(),
            trace: Vec::new(),
            tick: 0,
            policy,
            rng: StdRng::seed_from_u64(seed),
            instance_id,
        }
    }

    pub fn initiate(&mut self, broadcaster_id: ProcessId, value: Value) {
        let actions = self
            .honest
            .get_mut(&broadcaster_id)
            .expect("broadcaster must be honest")
            .initiate(value);
        self.enqueue_actions(broadcaster_id, actions);
    }

    pub fn inject_byzantine_messages(&mut self) {
        let all_ids = self.all_process_ids.clone();
        let instance_id = self.instance_id.clone();
        let tick = self.tick;

        for byz in &self.byzantine {
            let messages = byz.generate_messages(&instance_id, &all_ids);
            for (to, message) in messages {
                if self.honest.contains_key(&to) {
                    self.pending.push_back(Envelope {
                        from: byz.id,
                        to,
                        message,
                        deliver_at_tick: tick,
                    });
                }
            }
        }
    }

    pub fn run_until_quiescent(&mut self, max_ticks: u64) {
        while self.tick < max_ticks && !self.pending.is_empty() {
            self.tick();
        }
    }

    pub fn tick(&mut self) {
        self.tick += 1;
        let current_tick = self.tick;

        let mut due: Vec<Envelope> = Vec::new();
        let mut not_yet: VecDeque<Envelope> = VecDeque::new();
        while let Some(e) = self.pending.pop_front() {
            if e.deliver_at_tick <= current_tick {
                due.push(e);
            } else {
                not_yet.push_back(e);
            }
        }
        self.pending = not_yet;

        if let SchedulePolicy::Partition {
            ref side_a,
            ref side_b,
        } = self.policy
        {
            let sa = side_a.clone();
            let sb = side_b.clone();
            due.retain(|e| {
                !((sa.contains(&e.from) && sb.contains(&e.to))
                    || (sb.contains(&e.from) && sa.contains(&e.to)))
            });
        }

        if matches!(self.policy, SchedulePolicy::Random { .. }) {
            due.shuffle(&mut self.rng);
        }

        for envelope in due {
            self.deliver_envelope(envelope);
        }
    }

    fn deliver_envelope(&mut self, envelope: Envelope) {
        let Envelope {
            from, to, message, ..
        } = envelope;

        let process = match self.honest.get_mut(&to) {
            Some(p) => p,
            None => return,
        };

        let kind = message.kind().to_string();
        let value = message.value().clone();

        match process.handle_message(from, &message) {
            Ok(actions) => {
                self.trace.push(TraceEvent::new(
                    self.tick,
                    from,
                    Some(to),
                    &kind,
                    &value,
                    "ok",
                ));

                let mut new_actions = Vec::new();
                for action in &actions {
                    if let Action::Deliver { instance, value } = action {
                        self.deliveries.push(DeliveryEvent {
                            tick: self.tick,
                            process: to,
                            value: value.clone(),
                            instance: instance.clone(),
                        });
                        self.trace.push(TraceEvent::new(
                            self.tick,
                            to,
                            None,
                            "DELIVER",
                            value,
                            "delivered",
                        ));
                    }
                }
                new_actions.extend(actions);
                self.enqueue_actions(to, new_actions);
            }
            Err(e) => {
                self.trace.push(TraceEvent::new(
                    self.tick,
                    from,
                    Some(to),
                    &kind,
                    &value,
                    &format!("rejected: {e}"),
                ));
            }
        }
    }

    fn enqueue_actions(&mut self, from: ProcessId, actions: Vec<Action>) {
        let delay = match &self.policy {
            SchedulePolicy::DelayAll { ticks } => *ticks,
            _ => 0,
        };
        let deliver_at_tick = self.tick + delay;

        for action in actions {
            if let Action::Broadcast(message) = action {
                let targets: Vec<ProcessId> = self
                    .all_process_ids
                    .iter()
                    .copied()
                    .filter(|&id| id != from)
                    .collect();
                for to in targets {
                    self.pending.push_back(Envelope {
                        from,
                        to,
                        message: message.clone(),
                        deliver_at_tick,
                    });
                }
            }
        }
    }

    pub fn safety_holds(&self) -> bool {
        if self.deliveries.is_empty() {
            return true;
        }
        let first = &self.deliveries[0].value;
        self.deliveries.iter().all(|d| &d.value == first)
    }

    pub fn export_trace_json(&self) -> String {
        serde_json::to_string_pretty(&self.trace).unwrap_or_default()
    }

    pub fn delivered_values(&self) -> HashMap<ProcessId, Value> {
        let mut result = HashMap::new();
        for event in &self.deliveries {
            result.insert(event.process, event.value.clone());
        }
        result
    }
}
